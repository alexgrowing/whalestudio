import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsInertPlOfInertOff

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.Model

open GlobalTheory.AdelicU GlobalTheory.AdelicU.Supp

variable {D : D7}

local instance relAt (v : Pl D) : ValuativeRel (Fv D.host.F v) := GlobalTheory.LocalData.complRel v
local instance locAt (v : Pl D) : IsNonarchimedeanLocalField (Fv D.host.F v) := GlobalTheory.LocalData.isLocalField v

def secAt {v : Pl D} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : Fv D.host.F v →+ AE D :=
  AddMonoidHom.mk' (fun a => singleTens D.host.E v (a ⊗ₜ[D.host.F] (1 : D.host.E)) * splitIdemAd (isCMExt_host D) τ)
    fun a b => by rw [TensorProduct.add_tmul, map_add, add_mul]

def prAt {v : Pl D} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : AE D →+* Fv D.host.F v :=
  (splitProj τ).toRingHom.comp (GlobalTheory.AdelicU.compFin D.host.F D.host.E v)

theorem mem_int_iff {v : Pl D} (a : Fv D.host.F v) : a ∈ 𝒪[Fv D.host.F v] ↔ Valued.v a ≤ 1 := by
  have : (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [Valuation.mem_integer_iff,
    (isEquiv (valuation (Fv D.host.F v)) (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one]

def splitPt {v : Pl D} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : SplitPt D (Fv D.host.F v) where
  v := v
  e := splitIdemAd (isCMExt_host D) τ
  split := isSplitIdem_iff_exists.2 ⟨v, τ, rfl⟩
  above := ⟨_, isPlaceIdem_placeIdem D v, (splitAt_splitIdemAd τ).2.2⟩
  pr := prAt τ
  sec := secAt τ
  pr_sec a := by
    change splitProj τ (GlobalTheory.AdelicU.compFin _ _ v (singleTens _ v _ * singleTens _ v _)) = a
    rw [map_mul, compFin_singleTens_self, compFin_singleTens_self, map_mul, splitProj_tmul, splitProj_splitIdem, map_one,
      mul_one, mul_one]
  sec_pr x := (splitIdemAd_mul (isCMExt_host D) τ x).symm
  cont_pr := (continuous_splitProj τ).comp
    (GlobalTheory.AutFunCompare.continuous_tensNU (E := D.host.E) (evFin D.host.F v).toLinearMap (map_mul (evFin D.host.F v)) (by
      exact (RestrictedProduct.continuous_eval v).comp continuous_snd))
  cont_sec := by
    have h1 : Continuous fun a : AF D.host.F => (a ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) :=
      (continuous_id.smul (continuous_const (y := (1 : AE D)))).congr fun a => by
        change a • ((1 : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) = _
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    exact (h1.comp (Continuous.prodMk continuous_const (continuous_singleFin v))).mul continuous_const
  int_iff a := (mem_int_iff a).trans (GlobalTheory.IdemPrime.mem_iff (splitAt_splitIdemAd τ) a).symm

theorem exists_splitPt (D : D7) : ∃ v : Pl D, Nonempty (SplitPt D (Fv D.host.F v)) := by
  obtain ⟨v, ⟨τ⟩⟩ := exists_split_place (isCMExt_host D)
  exact ⟨v, ⟨splitPt τ⟩⟩

theorem isHermND (V : HSp D) : IsHermND D.sp.cm.sig V.gram :=
  ⟨fun i j => V.herm.eq (V.frame j) (V.frame i), (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).ne_zero⟩

def frame {v : Pl D} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (S : HSp D) (β : GL (Fin S.rank) (Fv D.host.F v)) :
    Frame (splitPt τ) S (Fin S.rank) where
  b := β.val
  b' := (β⁻¹).val
  bb' := β.mul_inv
  b'b := β.inv_mul
  gl := (emb D.sp.cm.sig S.gram v).comp
    (((splitEquiv (isCMExt_host D) (isHermND S) τ).symm : GL (Fin S.rank) (Fv D.host.F v) →* _).comp
      (MulAut.conj β).toMonoidHom)
  gl_supp g := (suppAt_splitIdemAd S τ _).2 ⟨_, rfl⟩
  gl_mat g := by
    have h := splitEquiv_val (isCMExt_host D) (isHermND S) τ
      (proj D.sp.cm.sig S.gram v (emb D.sp.cm.sig S.gram v ((splitEquiv (isCMExt_host D) (isHermND S) τ).symm (β * g * β⁻¹))))
    conv at h => lhs; rw [proj_emb_self, ContinuousMulEquiv.apply_symm_apply]
    exact h.symm

theorem gl_injective {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n) : Function.Injective β.gl := by
  intro g h e
  have h1 := β.gl_mat g
  rw [e, β.gl_mat] at h1
  have key : ∀ x : Matrix n n k, β.b' * (β.b * x * β.b') * β.b = x := fun x => by
    rw [Matrix.mul_assoc β.b, ← Matrix.mul_assoc β.b', β.b'b, Matrix.one_mul, Matrix.mul_assoc, β.b'b, Matrix.mul_one]
  exact Units.ext (by rw [← key g.val, ← h1, key])

theorem eq_single {v : Pl D} {a : AE D} (ha : a ∈ idAt D (· = v)) : a = singleTens D.host.E v (compAt D v a) := by
  have hc : ∀ u (z : AE D), GlobalTheory.AdelicU.compFin D.host.F D.host.E u z = compAt D u z := fun u z =>
    (tens_map_map (sndA D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F u) z).symm
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 ha
  refine adTens_ext (fun w => ?_) fun u => ?_
  · rw [compInf_singleTens]
    refine (tens_map_map (fstA D.host.F) (GlobalTheory.AutFunCompare.evW w) a).symm.trans ?_
    exact (congrArg (Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id D.host.F D.host.E)) h1).trans (map_zero _)
  · by_cases e : u = v
    · subst e; rw [compFin_singleTens_self, hc]
    · rw [compFin_singleTens_ne e, hc]
      exact (Submodule.mem_iInf _).1 h2 ⟨u, e⟩

theorem compAt_eq (u : Pl D) (z : AE D) : compAt D u z = GlobalTheory.AdelicU.compFin D.host.F D.host.E u z :=
  tens_map_map (sndA D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F u) z

theorem single_mem_idAt (v : Pl D) (y : Fv D.host.F v ⊗[D.host.F] D.host.E) : singleTens D.host.E v y ∈ idAt D (· = v) := by
  refine Submodule.mem_inf.2 ⟨?_, (Submodule.mem_iInf _).2 fun u => ?_⟩
  · induction y using TensorProduct.induction_on with
    | zero => exact (congrArg (infPart D) (singleTens D.host.E v).map_zero').trans (infPart D).map_zero
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
    | tmul a x => exact TensorProduct.zero_tmul _ x
  · exact (compAt_eq u.1 _).trans (compFin_singleTens_ne u.2 y)

theorem mem_idAt_iff {v : Pl D} {a : AE D} :
    a ∈ idAt D (· = v) ↔ algebraMap (AF D.host.F) (AE D) (placeIdem v) * a = a := by
  rw [← singleTens_one, singleTens_mul, one_mul, ← compAt_eq]
  exact ⟨fun h => (eq_single h).symm, fun h => h ▸ single_mem_idAt v _⟩

theorem mem_grpAt_iff {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S : HSp D) (g : GA D S) : g ∈ grpAt S (· = p.v) ↔ SuppAt p.e S g := by
  obtain ⟨ε, h1, h2⟩ := p.above
  obtain rfl := isPlaceIdem_iff.1 h1
  rw [SuppAt, h2]
  simp only [← mem_idAt_iff]
  rw [grpAt, congGrp, MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
  refine forall₂_congr fun i j => ?_
  rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
  have : Ideal.Quotient.mk (idAt D (· = p.v)) ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) =
      (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D ⧸ idAt D (· = p.v))) i j := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [this]
  exact Iff.rfl

theorem tame {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) : Tame D p.v := by
  obtain ⟨ε, h1, h2⟩ := p.above
  exact ⟨fun P hP _ => Algebra.unramified_iff_forall.1 (GlobalTheory.InertOfConj.unram D) ⟨P, hP⟩,
    Or.inr ⟨p.e, ε, p.split, h1, h2⟩⟩

def intGrp (D : D7) (v : Pl D) : AddSubgroup (AE D) :=
  (idAt D (· = v)).toAddSubgroup ⊓ (intAE D).comap (finPart D).toAddMonoidHom

theorem latV_le_int (S : HSp D) (L : Lat S) (hL : ∀ x ∈ L, ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = x i) (v : Pl D) :
    latV S L (· = v) ≤ AddSubgroup.pi Set.univ fun _ => intGrp D v := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, h0, a, rfl, x, hx, rfl⟩ i -
  obtain ⟨b, hb⟩ := hL x hx i
  refine ⟨Submodule.mem_inf.2 ⟨TensorProduct.zero_tmul _ _, (Submodule.mem_iInf _).2 fun u => ?_⟩,
    AddSubgroup.subset_closure ⟨α, hα, b, by rw [hb, ← one_mul (x i)]; rfl⟩⟩
  change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F u.1 α ⊗ₜ[D.host.F] _ = 0
  rw [h0 _ u.2, TensorProduct.zero_tmul]

theorem single_mem_latV (S : HSp D) (L : Lat S) (v : Pl D) (i : Fin S.rank)
    (hL : ∀ b : 𝓞 D.host.E, Pi.single i (b : D.host.E) ∈ L) :
    intAE D ≤ (latV S L (· = v)).comap ((AddMonoidHom.single (fun _ : Fin S.rank => AE D) i).comp
      ((singleTens D.host.E v).toAddMonoidHom.comp (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v).toAddMonoidHom)) := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, b, rfl⟩
  refine AddSubgroup.subset_closure ⟨singleFin v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v α), fun u => ?_,
    fun u hu => evalV_singleFin_ne hu _, 1, rfl, Pi.single i (b : D.host.E), hL b, funext fun j => ?_⟩
  · by_cases e : u = v
    · subst e; rw [evalV_singleFin_self]; exact hα u
    · rw [evalV_singleFin_ne e]; exact zero_mem _
  · change (Pi.single i (pairA D.host.F 0 (singleFin v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v α)) ⊗ₜ[D.host.F] (b : D.host.E)) :
      Fin S.rank → AE D) j = _
    by_cases e : j = i
    · subst e; rw [Pi.single_eq_same, Pi.single_eq_same, one_mul]
    · rw [Pi.single_eq_of_ne e, Pi.single_eq_of_ne e, mul_zero, TensorProduct.tmul_zero]

theorem mem_latV_std (S : HSp D) (L : Lat S) (hL : ∀ x, x ∈ L ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = x i) (v : Pl D)
    (y : Fin S.rank → AE D) : y ∈ latV S L (· = v) ↔ ∀ i, y i ∈ intAt D (· = v) := by
  refine ⟨fun hy i => latV_le_int S L (fun x => (hL x).1) v hy i trivial, fun hy => ?_⟩
  rw [← Finset.univ_sum_single y]
  refine sum_mem fun i _ => ?_
  rw [eq_single (hy i).1]
  refine single_mem_latV S L v i (fun b => (hL _).2 fun j => ?_) (hy i).2
  by_cases e : j = i
  · subst e; exact ⟨b, by rw [Pi.single_eq_same]⟩
  · exact ⟨0, by rw [Pi.single_eq_of_ne e]; rfl⟩

theorem isLat_std {v : Pl D} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (S : HSp D) (L : Lat S)
    (hL : ∀ x, x ∈ L ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = x i) :
    (frame τ S 1).IsLat L (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[Fv D.host.F v] (Fv D.host.F v))) := fun x => by
  rw [mem_latV_std S L hL, Submodule.mem_pi]
  refine forall_congr' fun i => ?_
  have e : ((frame τ S 1).b *ᵥ x) = x := Matrix.one_mulVec x
  rw [e]
  have h1 : (splitPt τ).sec (x i) ∈ idAt D (· = v) := Ideal.mul_mem_right _ _ (single_mem_idAt v _)
  rw [show (splitPt τ).sec (x i) ∈ intAt D (· = (splitPt τ).v) ↔ _ from and_iff_right h1, ← (splitPt τ).int_iff,
    Submodule.mem_one]
  exact ⟨fun h => let ⟨b, hb⟩ := h trivial; hb ▸ b.2, fun h _ => ⟨⟨_, h⟩, rfl⟩⟩

theorem integrand_dual {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (ψ : AddChar (AF D.host.F) ℂ) (f : WO V W → ℂ)
    (x a a' : Mx D W.rank ρ) (w₀ : WO V₀ W) :
    heisO ψ V W (d.extY W a') (heisO ψ V W (d.extX W x) (heisO ψ V W (d.ext0 W w₀) (heisO ψ V W (d.extY W a) f))) 0 =
      ψ (symplOH V W (d.extX W x) (d.extY W a) + symplOH V W (d.extX W x) (d.extY W a)) *
        heisO ψ V W (d.extY W (a' + a)) (heisO ψ V W (d.extX W x) (heisO ψ V W (d.ext0 W w₀) f)) 0 := by
  rw [d.integrandS_eq, d.integrandS_eq, heisO, map_add (d.extY W), ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul,
    ← AddChar.map_add_eq_mul]
  have h0 : symplOH V W (d.ext0 W w₀) (d.extY W a) = 0 := by
    rw [symplOH_skew, d.wittDecomp_sympl_extDual_extAnisotropic, neg_zero]
  simp only [GlobalTheory.OrientedHeis.symplOH_add_left, d.symplOH_extY_extY, h0, zero_add, add_zero]
  rw [symplOH_skew V W (d.extX W x) (d.extY W a)]
  congr 2
  · ring
  · abel

end GlobalTheory.FinPl.Model

end
