import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMtTieCoord
import Formalism.LocalToGlobal.Divisibility.RowSideTie

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.DivisionValues
open Formalism.IndefR.Cx
open scoped InnerProductSpace Matrix

namespace GlobalTheory.Mem.LiftTheta

section Core

variable {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {N H : Type} [AddCommGroup N] [Module ℂ N] [AddCommGroup H] [Module ℂ H]

omit [NumberField K] in
theorem semi_expand {d : ℕ} (w : (Fin d → K) →ₛₗ[σ] H) (y : Fin d → K) : w y = ∑ k, σ (y k) • w (Pi.single k 1) := by
  have hz : y = ∑ k, y k • (Pi.single k 1 : Fin d → K) := by
    ext i; simp [Pi.single_apply]
  conv_lhs => rw [hz]
  simp only [map_sum, map_smulₛₗ]

omit [NumberField K] in
theorem semi_injective {d : ℕ} (w : (Fin d → K) →ₛₗ[σ] H) (hli : LinearIndependent ℂ fun k => w (Pi.single k 1)) :
    Function.Injective w := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  rw [semi_expand] at hy
  funext k
  exact (map_eq_zero σ).1 (Fintype.linearIndependent_iff.1 hli _ hy k)

omit [NumberField K] in

theorem exists_form {d : ℕ} (e : N →ₗ[ℂ] H) (he : Function.Injective e) (w : (Fin d → K) →ₛₗ[σ] H)
    (hli : LinearIndependent ℂ fun k => w (Pi.single k 1))
    (hsp : Submodule.span ℂ (Set.range fun k => w (Pi.single k 1)) = LinearMap.range e) :
    ∃ j : (Fin d → K) →ₛₗ[σ] N, (∀ y, e (j y) = w y) ∧ (LinearIndependent ℂ fun k => j (Pi.single k 1)) ∧
      Submodule.span ℂ (Set.range fun k => j (Pi.single k 1)) = ⊤ := by
  have hex : ∀ y, ∃ n, e n = w y := by
    intro y
    have : w y ∈ LinearMap.range e := by
      rw [← hsp, semi_expand]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    exact this
  choose g hg using hex
  let j : (Fin d → K) →ₛₗ[σ] N :=
    { toFun := g
      map_add' := fun x y => he (by simp only [map_add, hg])
      map_smul' := fun a x => he (by simp only [map_smulₛₗ, hg, RingHom.id_apply]) }
  have hj : ∀ y, e (j y) = w y := hg
  refine ⟨j, hj, LinearIndependent.of_comp e ?_, ?_⟩
  · have : (e ∘ fun k => j (Pi.single k 1)) = fun k => w (Pi.single k 1) := funext fun k => hj _
    rw [this]; exact hli
  · apply Submodule.map_injective_of_injective he
    rw [Submodule.map_top, ← hsp, Submodule.map_span, ← Set.range_comp]
    congr 2
    exact funext fun k => hj _

theorem oLatTie_of_closure {O : Type} [CommRing O] {φ : O →+* ℂ} (hφ : ∀ a, ∃ b : 𝓞 K, φ a = σ (b : K))
    (M : Rows.OLat O φ N) {d : ℕ} (e : N →ₗ[ℂ] H) (he : Function.Injective e) (j : (Fin d → K) →ₛₗ[σ] N)
    (hj : Function.Injective j) (L : Submodule (𝓞 K) (Fin d → K)) (S : Set H) (hS : ∀ y, y ∈ S ↔ ∃ x ∈ L, e (j x) = y)
    (h : AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ e '' M.carrier, y = σ (a : K) • x} =
      AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ S, y = σ (a : K) • x}) :
    OLatTie σ M j L := by
  classical
  have hR : ∀ y, y ∈ AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ S, y = σ (a : K) • x} ↔ ∃ x ∈ L, e (j x) = y := by
    intro y
    refine ⟨fun hy => ?_, fun hy => AddSubgroup.subset_closure ⟨1, y, (hS y).2 hy, by simp⟩⟩
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, u, hu, rfl⟩ := hy
      obtain ⟨x, hx, rfl⟩ := (hS u).1 hu
      refine ⟨a • x, L.smul_mem a hx, ?_⟩
      rw [← algebraMap_smul K a x, map_smulₛₗ, map_smul]
    | zero => exact ⟨0, L.zero_mem, by simp⟩
    | add _ _ _ _ h1 h2 =>
      obtain ⟨x, hx, rfl⟩ := h1
      obtain ⟨x', hx', rfl⟩ := h2
      exact ⟨x + x', L.add_mem hx hx', by simp⟩
    | neg _ _ h1 =>
      obtain ⟨x, hx, rfl⟩ := h1
      exact ⟨-x, L.neg_mem hx, by simp⟩
  have hgen : ∀ v ∈ M.gen, v ∈ M.carrier := by
    intro v hv
    refine ⟨fun u => if u = v then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single v]
    · simp
    · intro u _ hu
      simp [hu]
    · intro h; exact absurd hv h
  have hL : ∀ y, y ∈ AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ e '' M.carrier, y = σ (a : K) • x} ↔
      ∃ c : N → 𝓞 K, y = e (∑ v ∈ M.gen, σ (c v : K) • v) := by
    intro y
    constructor
    · intro hy
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, _, ⟨_, ⟨c, rfl⟩, rfl⟩, rfl⟩ := hy
        choose b hb using hφ
        refine ⟨fun v => a * b (c v), ?_⟩
        rw [← map_smul, Finset.smul_sum]
        simp [hb, mul_smul]
      | zero => exact ⟨0, by simp⟩
      | add _ _ _ _ h1 h2 =>
        obtain ⟨c, rfl⟩ := h1
        obtain ⟨c', rfl⟩ := h2
        refine ⟨c + c', ?_⟩
        rw [← map_add, ← Finset.sum_add_distrib]
        simp [add_smul]
      | neg _ _ h1 =>
        obtain ⟨c, rfl⟩ := h1
        refine ⟨-c, ?_⟩
        rw [← map_neg, ← Finset.sum_neg_distrib]
        simp
    · rintro ⟨c, rfl⟩
      rw [map_sum]
      refine AddSubgroup.sum_mem _ fun v hv => AddSubgroup.subset_closure ⟨c v, e v, ⟨v, hgen v hv, rfl⟩, map_smul _ _ _⟩
  refine ⟨fun v hv => ?_, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · have h1 : e v ∈ AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ e '' M.carrier, y = σ (a : K) • x} :=
      AddSubgroup.subset_closure ⟨1, e v, ⟨v, hgen v hv, rfl⟩, by simp⟩
    rw [h, hR] at h1
    obtain ⟨x, -, hx⟩ := h1
    exact ⟨x, he hx⟩
  · have h1 := (hR _).2 ⟨x, hx, rfl⟩
    rw [← h, hL] at h1
    obtain ⟨c, hc⟩ := h1
    exact ⟨c, he hc⟩
  · rintro ⟨c, hc⟩
    have h1 := (hL (e (j x))).2 ⟨c, congrArg e hc⟩
    rw [h, hR] at h1
    obtain ⟨x', hx', hxx⟩ := h1
    rwa [← hj (he hxx)]

theorem map_eq_map_proj [StarRing K] {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M]
    (th : M →ₗ[ℂ] N) {n d : ℕ} (J : (Fin n → K) →ₛₗ[σ] M) {Hm : Matrix (Fin n) (Fin n) K} {E : Matrix (Fin n) (Fin d) K}
    {Pr : Matrix (Fin d) (Fin n) K} (hp : IsOrthProj Hm E Pr) (hin : ∀ x y, inner ℂ (J x) (J y) = σ (hform Hm x y))
    (hle : Submodule.span ℂ (Set.range fun k => J (E *ᵥ Pi.single k 1)) ≤ (LinearMap.ker th)ᗮ)
    (hsur : ∀ y, th y ∈ Submodule.span ℂ (Set.range fun k => th (J (E *ᵥ Pi.single k 1)))) (x : Fin n → K) :
    th (J x) = th (J (E *ᵥ (Pr *ᵥ x))) := by
  have hge : (LinearMap.ker th)ᗮ ≤ Submodule.span ℂ (Set.range fun k => J (E *ᵥ Pi.single k 1)) := by
    intro y hy
    have h1 := hsur y
    rw [show (fun k => th (J (E *ᵥ Pi.single k 1))) = th ∘ fun k => J (E *ᵥ Pi.single k 1) from rfl, Set.range_comp,
      ← Submodule.map_span] at h1
    obtain ⟨z, hz, hzy⟩ := h1
    have h2 : y - z ∈ LinearMap.ker th := by rw [LinearMap.mem_ker, map_sub, hzy, sub_self]
    have h3 : y - z ∈ (LinearMap.ker th)ᗮ := sub_mem hy (hle hz)
    have h4 : y - z = 0 := inner_self_eq_zero.1 (h3 _ h2)
    rw [sub_eq_zero.1 h4]
    exact hz
  rw [← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, ← Submodule.orthogonal_orthogonal (LinearMap.ker th)]
  intro u hu
  have h5 : Submodule.span ℂ (Set.range fun k => J (E *ᵥ Pi.single k 1)) ≤
      (Submodule.span ℂ {J x - J (E *ᵥ (Pr *ᵥ x))})ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_right, hin, hin,
      LiftForms.hform_orth hp, sub_self]
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 (h5 (hge hu))

omit [NumberField K] in
theorem lin_cpt {d : ℕ} (w : (Fin d → K) →ₛₗ[σ] H) (y : Fin d → K) :
    lin (fun k => w (Pi.single k 1)) (cpt σ y) = w y := (semi_expand w y).symm

end Core

section Lift

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
  {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

theorem liftMatrix_computes_lift_rational (h5 : X.H5 cr b) (hr : X.RATth cr b) (j : Bs.J) (t : Bs.Tup) (z : Fin ((lv (fc X.zs) b).dZ j t) → K) :
    X.w0C b j (cpt Bs.v0.embedding (X.liftMat cr b j t *ᵥ z)) = X.θ' j t (X.jL j t (cr.toL X.zs b j t z)) :=
  (X.key_lift cr b h5 hr j t z).trans (lin_cpt (((X.θ' j t).comp (X.jL j t)).comp (cr.toL X.zs b j t)) z)

end Lift

section Main

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem thTie_of_clauses {s : ℕ} (hOk : A.fam.Ok s) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb)
    (S0 : IndefData (A.side P ψ Zs)) (tup : T → D.what₂.Tup)
    (eMt : ∀ (i : Fin D.R.m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1))
    (hM : MtTie D A P ψ Zs tup eMt) {H : Fin D.R.m → Type} [∀ i, AddCommGroup (H i)] [∀ i, Module ℂ (H i)]
    (e : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] H i) (he : ∀ i, Function.Injective (e i))
    (w : ∀ i : Fin D.R.m, (Fin (S0.dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] H i)
    (hli : ∀ i, LinearIndependent ℂ fun k => w i (Pi.single k 1))
    (hsp : ∀ i, Submodule.span ℂ (Set.range fun k => w i (Pi.single k 1)) = LinearMap.range (e i))
    (S : ∀ i, Set (H i)) (hS : ∀ i y, y ∈ S i ↔ ∃ x ∈ S0.M i, w i x = y)
    (hlat : ∀ i, intSpan D (e i '' (D.what₂.MjLat ((i : ℕ) + 1)).carrier) = intSpan D (S i))
    (hth : ∀ i t z, w i (S0.θ i t *ᵥ z) = e i (D.what₂.thetaP (tup t) ((i : ℕ) + 1)
      (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t (lZ0 D A P ψ Zs i t *ᵥ z)))))
    (hsur : ∀ i t, Function.Surjective (S0.θ i t).mulVec) :
    ∃ jW, ThTie D A S0 tup eMt jW ∧ ∀ i y, e i (jW i y) = w i y := by
  choose jW hj hjli hjsp using fun i => exists_form (e i) (he i) (w i) (hli i) (hsp i)
  have hth' : ∀ i t z, jW i (S0.θ i t *ᵥ z) = D.what₂.thetaP (tup t) ((i : ℕ) + 1)
      (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t (lZ0 D A P ψ Zs i t *ᵥ z))) :=
    fun i t z => he i ((hj i _).trans (hth i t z))
  refine ⟨jW, ⟨hjli, hjsp, fun i => ?_, fun i t x => ?_⟩, hj⟩
  · refine oLatTie_of_closure (fun a => ⟨⟨D.what₂.OtoLL a, D.O_int a⟩, rfl⟩) _ (e i) (he i) (jW i)
      (semi_injective _ (hjli i)) _ (S i) (fun y => ?_) (hlat i)
    simp only [hj]
    exact hS i y
  · have hB : BlockHyp (A.fam.L i t) (A.fam.lvlA P ψ) A.v0 s := ⟨hOk.conj, hOk.irr, hOk.lifts i t⟩
    have hp : IsOrthProj (lH D A P ψ i t) (lZ0 D A P ψ Zs i t) (lPrj D A P ψ Zs i t) := BlockDat.lf_l_proj hB
    rw [hth']
    refine map_eq_map_proj (D.what₂.thetaP (tup t) ((i : ℕ) + 1))
      ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) hp (hM.forms i t).inner ?_ (fun y => ?_) x
    · exact (hM.Z0 i t).ge.trans inf_le_left
    · have hle : Submodule.span ℂ (Set.range fun k => jW i (Pi.single k 1)) ≤ Submodule.span ℂ (Set.range fun k =>
          D.what₂.thetaP (tup t) ((i : ℕ) + 1)
            (((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lZ0 D A P ψ Zs i t *ᵥ Pi.single k 1))) := by
        rw [Submodule.span_le]
        rintro _ ⟨k, rfl⟩
        obtain ⟨z, hz⟩ := hsur i t (Pi.single k 1)
        have h1 := (LiftForms.span_range_mulVec ((D.what₂.thetaP (tup t) ((i : ℕ) + 1)).comp
          ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap)) (lZ0 D A P ψ Zs i t)).le
        refine h1 (Submodule.subset_span ⟨_, ⟨z, rfl⟩, ?_⟩)
        exact (hth' i t z).symm.trans (congrArg (jW i) hz)
      exact hle (hjsp i ▸ Submodule.mem_top)

variable (R : RealDat D A Ks) (F : Face D A)

def goodForm (b : Bool) (i : Fin D.R.m) :
    (Fin (Module.finrank D.what₂.LL (R.WL F b i)) → D.what₂.LL) →ₛₗ[D.what₂.embLL] (R.HW i (sg0 D A)).H where
  toFun y := (R.FW i).j (sg0 D A) (∑ k, y k • R.bL F b i k)
  map_add' x y := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, map_add]
  map_smul' a y := by
    have h : sg0 D A a = D.what₂.embLL a := by rw [sg0, sgAt_mk _ R.hv0]
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, map_smulₛₗ, h]

theorem goodForm_apply (b : Bool) (i : Fin D.R.m) (y : Fin (Module.finrank D.what₂.LL (R.WL F b i)) → D.what₂.LL) :
    goodForm R F b i y = (R.FW i).j (sg0 D A) (∑ k, y k • R.bL F b i k) := rfl

theorem goodForm_single (b : Bool) (i : Fin D.R.m) (k : Fin (Module.finrank D.what₂.LL (R.WL F b i))) :
    goodForm R F b i (Pi.single k 1) = (R.FW i).j (sg0 D A) (R.bL F b i k) := by
  rw [goodForm_apply]
  congr 1
  simp [Pi.single_apply]

theorem goodForm_li (hU : R.LUnif) (b : Bool) (i : Fin D.R.m) :
    LinearIndependent ℂ fun k => goodForm R F b i (Pi.single k 1) := by
  simp only [goodForm_single]
  exact (hU i _).1 _ _
    ((Module.finBasis D.what₂.LL (R.WL F b i)).linearIndependent.map' (R.WL F b i).subtype (Submodule.ker_subtype _))

theorem sqrt_ne (b : Bool) : ((Real.sqrt (RealDat.nP F b) : ℝ) : ℂ) ≠ 0 := by
  have := Real.sqrt_pos.2 (RealDat.nP_pos (F := F) b)
  exact_mod_cast this.ne'

theorem smul_bC (b : Bool) (i : Fin D.R.m) (k : Fin (Module.finrank D.what₂.LL (R.WL F b i))) :
    ((Real.sqrt (RealDat.nP F b) : ℝ) : ℂ) • R.bC F b i (sg0 D A) k = goodForm R F b i (Pi.single k 1) := by
  rw [goodForm_single, RealDat.bC, smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ (sqrt_ne F b), one_smul]

theorem goodForm_span (b : Bool) (i : Fin D.R.m) :
    Submodule.span ℂ (Set.range fun k => goodForm R F b i (Pi.single k 1)) = R.WS F b i (sg0 D A) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe]
    beta_reduce
    rw [← smul_bC]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rw [RealDat.WS, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, ← Submodule.smul_mem_iff _ (sqrt_ne F b), smul_bC]
    exact Submodule.subset_span ⟨k, rfl⟩

theorem mem_image_iff (b : Bool) (i : Fin D.R.m) (y : (R.HW i (sg0 D A)).H) :
    y ∈ (R.FW i).j (sg0 D A) '' ((R.FW i).Mj (F.lvl b).P (F.lvl b).ψ⁻¹ (fun g => (idemOf A.X).coeff g) : Set _) ↔
      ∃ x ∈ (R.toCx F).M b i, goodForm R F b i x = y := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    have hW : f ∈ R.WL F b i := (R.FW i).Mj_sub_Wgood _ _ _ hf
    have hs : ∑ k, (Module.finBasis D.what₂.LL (R.WL F b i)).repr ⟨f, hW⟩ k • R.bL F b i k = f := by
      have h := congrArg (R.WL F b i).subtype ((Module.finBasis D.what₂.LL (R.WL F b i)).sum_repr ⟨f, hW⟩)
      rw [map_sum] at h
      exact h
    refine ⟨fun k => (Module.finBasis D.what₂.LL (R.WL F b i)).repr ⟨f, hW⟩ k, ((R.FW i).mem_Mcoord _ _ _ _ _).2 ?_, ?_⟩
    · rw [hs]; exact hf
    · exact congrArg ((R.FW i).j (sg0 D A)) hs
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ((R.FW i).mem_Mcoord _ _ _ _ _).1 hx, rfl⟩

theorem liftWeight_complexPoint_eq_twist (b : Bool) (i : Fin D.R.m) (y : Fin (Module.finrank D.what₂.LL (R.WL F b i)) → D.what₂.LL) :
    (R.toCx F).w0C b i (cpt A.v0.embedding y) = Tw.mk (twAt D.what₂.embLL A.v0) (goodForm R F b i y) := by
  have h1 : (R.toCx F).w0C b i = lin fun k => Tw.semi _ R.emb0 (goodForm R F b i) (Pi.single k 1) := by
    rw [← lin_basis ((R.toCx F).w0C b i)]
    congr 1
    funext k
    exact (congrArg ((R.toCx F).eW b i) (lin_single _ k)).trans (smul_bC R F b i k)
  rw [h1]
  exact lin_cpt (Tw.semi _ R.emb0 (goodForm R F b i)) y

theorem levelFormCoordinateMap_levelZero {s : ℕ} (hOk : A.fam.Ok s) (Zs : DefSub A.fam.amb) (i : Fin D.R.m) (t : T)
    (z : Fin ((A.fam.L i t).dZ (A.fam.lvlA F.P0 F.ψ0) (Zs.Zl i t)) → D.what₂.LL) :
    LiftForms.lvlForm (A.fam.L i t).S (A.fam.L i t).r (A.fam.lvlA F.P0 F.ψ0).P (A.fam.lvlA F.P0 F.ψ0).ψ
      (lZ0 D A F.P0 F.ψ0 Zs i t *ᵥ z) = F.cr.toL Zs false i t z :=
  LiftForms.lvlForm_lE (v0 := A.v0) (s := s) ⟨hOk.conj, hOk.irr, hOk.lifts i t⟩ z

set_option maxHeartbeats 1000000 in

theorem exists_thTie_of_coord {s : ℕ} (X0 : BaseLevelRowSide D) (hOk : A.fam.Ok s) (hU : R.LUnif) (hL : R.LLevelW F) (hT : R.LTheta F)
    (hR : R.LRatTh F) (Y : RowsTie R F X0)
    (eMt : ∀ (i : Fin D.R.m) (t : T),
      (Fin (lDim D A F.P0 F.ψ0 i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (Y.tup t) ((i : ℕ) + 1))
    (hM : MtTie D A F.P0 F.ψ0 (R.toCx F).zs Y.tup eMt)
    (hco : ∀ (i : Fin D.R.m) (t : T) x, Y.eV i t (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (eMt i t x)) =
      R.jV i t (LiftForms.lvlForm (A.fam.L i t).S (A.fam.L i t).r (A.fam.lvlA F.P0 F.ψ0).P (A.fam.lvlA F.P0 F.ψ0).ψ x)) :
    ∃ jW, ThTie D A (P0 := F.P0) (ψ0 := F.ψ0) (Zs := (R.toCx F).zs) ((R.toCx F).data F.cr false) Y.tup eMt jW ∧
      ∀ i y, Y.eW i (jW i y) = goodForm R F false i y := by
  refine thTie_of_clauses hOk F.P0 F.ψ0 (R.toCx F).zs ((R.toCx F).data F.cr false) Y.tup eMt hM Y.eW Y.eW_injective
    (goodForm R F false) (goodForm_li R F hU false) (fun i => ?_) _ (mem_image_iff R F false) Y.eW_lat (fun i t z => ?_)
    (fun i t => ((R.toCx F).liftMat_bij F.cr false (RealDat.kForm hU false) (RealDat.ewNorm false) (RealDat.nP_pos false)
      (hT false) (hR false) i t).2)
  · exact (goodForm_span R F false i).trans ((hL false i _).trans (Y.eW_range i).symm)
  · have h1 := (liftWeight_complexPoint_eq_twist R F false i _).symm.trans (liftMatrix_computes_lift_rational (R.toCx F) F.cr false (hT false) (hR false) i t z)
    have h2 := (Y.theta_tie i t _).trans (congrArg (R.thG i t) ((hco i t _).trans
      (congrArg (R.jV i t) (levelFormCoordinateMap_levelZero F hOk (R.toCx F).zs i t z))))
    exact h1.trans h2.symm

theorem exists_mtTie_thTie {s : ℕ} (X0 : BaseLevelRowSide D) (hC : R.Char F) (hOk : A.fam.Ok s) (hZ : R.LRatZ F) (hS : R.LStable F)
    (hU : R.LUnif) (hL : R.LLevelW F) (hT : R.LTheta F) (hR : R.LRatTh F) (Y : RowsTie R F X0) :
    ∃ eMt jW, MtTie D A F.P0 F.ψ0 (R.toCx F).zs Y.tup eMt ∧
      ThTie D A (P0 := F.P0) (ψ0 := F.ψ0) (Zs := (R.toCx F).zs) ((R.toCx F).data F.cr false) Y.tup eMt jW ∧
      (∀ (i : Fin D.R.m) (t : T) x, Y.eV i t (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (eMt i t x)) =
        R.jV i t (LiftForms.lvlForm (A.fam.L i t).S (A.fam.L i t).r (A.fam.lvlA F.P0 F.ψ0).P (A.fam.lvlA F.P0 F.ψ0).ψ x)) ∧
      ∀ i y, Y.eW i (jW i y) = goodForm R F false i y := by
  have h := LiftForms.exists_mtTie_coord R F X0 hC hOk hZ hS Y
  refine h.elim fun e he => ?_
  have h' := exists_thTie_of_coord R F X0 hOk hU hL hT hR Y e he.1 fun i t => (he.2 i t).1
  exact h'.elim fun jW hj => ⟨e, jW, he.1, hj.1, fun i t => (he.2 i t).1, hj.2⟩

end Main

end GlobalTheory.Mem.LiftTheta

end
