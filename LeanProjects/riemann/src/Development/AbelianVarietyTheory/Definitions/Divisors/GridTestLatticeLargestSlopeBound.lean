import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.IsCyclotomicExtensionFourSlopeModelField
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV Formalism.UG
open GlobalTheory.ChiGrid GlobalTheory.TestLat
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Delta

variable {Γ A K M : Type} [Group Γ] [Group A] [Field K] [AddCommGroup M] [Module K M]
  (ι : Γ →* A) (U : Subgroup A) (ρ : Γ →* Module.End K M)

open Classical in

def deltaForm (x : A) (v : M) (g : A) : M := ∑ᶠ γ : Γ, if x⁻¹ * ((ι γ)⁻¹ * g) ∈ U then ρ γ v else 0

theorem deltaForm_left (x : A) (v : M) (δ : Γ) (g : A) :
    deltaForm ι U ρ x v (ι δ * g) = ρ δ (deltaForm ι U ρ x v g) := by
  classical
  have hinj : Function.Injective (ρ δ) := Function.LeftInverse.injective (g := ρ δ⁻¹) fun y => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  unfold deltaForm
  rw [← finsum_comp_equiv (Equiv.mulLeft δ)]
  refine Eq.trans (finsum_congr fun γ => ?_) ((ρ δ).toAddMonoidHom.map_finsum_of_injective hinj _).symm
  simp only [Equiv.coe_mulLeft, map_mul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left, LinearMap.toAddMonoidHom_coe]
  split_ifs <;> simp

theorem deltaForm_right (x : A) (v : M) (g : A) {u : A} (hu : u ∈ U) :
    deltaForm ι U ρ x v (g * u) = deltaForm ι U ρ x v g := by
  unfold deltaForm
  refine finsum_congr fun γ => ?_
  have : x⁻¹ * ((ι γ)⁻¹ * (g * u)) ∈ U ↔ x⁻¹ * ((ι γ)⁻¹ * g) ∈ U := by
    rw [← mul_assoc _ g, ← mul_assoc x⁻¹, U.mul_mem_cancel_right hu]
  exact propext this ▸ rfl

theorem deltaForm_self (x : A) (v : M) (h : ∀ γ, x⁻¹ * ι γ * x ∈ U → γ = 1) : deltaForm ι U ρ x v x = v := by
  unfold deltaForm
  rw [finsum_eq_single _ 1 fun γ hγ => if_neg fun hm => hγ (inv_eq_one.1 (h γ⁻¹ (by rwa [map_inv, mul_assoc])))]
  simp [U.one_mem]

theorem deltaForm_eq_zero (x : A) (v : M) (g : A) (h : ∀ γ, ∀ u ∈ U, g ≠ ι γ * x * u) : deltaForm ι U ρ x v g = 0 := by
  unfold deltaForm
  refine finsum_eq_zero_of_forall_eq_zero fun γ => if_neg fun hm => h γ _ hm ?_
  simp [mul_assoc]

end Delta

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GlobalTheory.ChiGrid.GridData L sc)

abbrev Xp : HSp D := G.V (.top 0)

theorem isV_Xp : (G.node (.top 0)).IsV (rankP D D.R.m) 0 := by
  have := G.sp.P_is D.R.m le_rfl
  rwa [Nat.sub_self] at this

theorem rank_Xp : (Xp G).rank = rankP D D.R.m := (isV_Xp G).rank

def LaP (τ : D.what₂.Tau) : DomWeight (Xp G).rank where
  w a := (La D sc.cGap τ).w (Fin.cast (rank_Xp G) a)
  anti _ _ h := (La D sc.cGap τ).anti h

variable (D) in

abbrev emb : D.what₂.Tau → D.host.E →+* D.what₂.LL := labLL D

abbrev WtSp : Type := VV D.what₂.LL (LaP G)

abbrev GLf : Type := GL (Fin (Xp G).rank) (Formalism.IndefR.Lev.EAf D)

abbrev TestIx : Type := G.Datum × G.ClPlus

structure ClassReps where

  x : G.ClPlus → UA D.sp.cm (Xp G).gram

  classRepresentative_mk : ∀ c, (Quotient.mk'' (x c) : G.ClPlus) = c

instance : Inhabited (ClassReps G) := ⟨⟨rep, mk_rep⟩⟩

def latOf (g : GLf G) : Submodule (𝓞 D.host.E) (Fin (Xp G).rank → D.host.E) := CS.globLat g (G.Λ (.top 0))

abbrev wLat (Λ : Submodule (𝓞 D.host.E) (Fin (Xp G).rank → D.host.E)) : Submodule (𝓞 D.what₂.LL) (WtSp G) :=
  delAtr (emb D) (LaP G) Λ

def rhoW : UR D.sp.cm (Xp G).gram →* Module.End D.what₂.LL (WtSp G) :=
  (rhoVr (emb D) (LaP G)).comp (UR D.sp.cm (Xp G).gram).subtype

def ratIn : UR D.sp.cm (Xp G).gram →* GLf G :=
  (bc (inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))).comp (UR D.sp.cm (Xp G).gram).subtype

variable {G}

def ClassReps.lat (rp : ClassReps G) (c : G.ClPlus) : Submodule (𝓞 D.host.E) (Fin (Xp G).rank → D.host.E) := latOf G (rp.x c)

def ClassReps.Neat (rp : ClassReps G) : Prop :=
  ∀ c γ, ((rp.x c : GLf G))⁻¹ * ratIn G γ * rp.x c ∈ G.Kplus → γ = 1

variable (G)

def formLat (rp : ClassReps G) {n : ℕ} (e : Fin n ≃ TestIx G × VVIdx (LaP G)) : Submodule (𝓞 D.what₂.LL) (Fin n → D.what₂.LL) :=
  GlobalTheory.TestLat.sumLat (LaP G) e fun c => wLat G (rp.lat c.2)

def formGram {n : ℕ} (e : Fin n ≃ TestIx G × VVIdx (LaP G)) : Matrix (Fin n) (Fin n) D.what₂.LL :=
  sumGram (LaP G) e (gramKd (emb D) (Xp G).gram)

def IsTestLat (rp : ClassReps G) (n : ℕ) (e : Fin n ≃ TestIx G × VVIdx (LaP G))
    (X' : InfinitePlace D.what₂.LL → Matrix (Fin n) (Fin n) ℂ) (M : Submodule (𝓞 D.what₂.LL) (Fin n → D.what₂.LL)) : Prop :=
  IsMetric ((formGram G e)⁻¹)ᵀ X' ∧ M = dualFr (formLat G rp e)

variable {G}

def ClassReps.delta (rp : ClassReps G) (c : G.ClPlus) (v : WtSp G) : GLf G → WtSp G :=
  deltaForm (ratIn G) G.Kplus (rhoW G) (rp.x c) v

def datumOf {n : ℕ} (e : Fin n ≃ TestIx G × VVIdx (LaP G)) (a : Fin n) : G.Datum := (e a).1.1

def psi (rp : ClassReps G) {n : ℕ} (e : Fin n ≃ TestIx G × VVIdx (LaP G)) (a : Fin n) : GLf G → WtSp G :=
  rp.delta (e a).1.2 (bVV D.what₂.LL (LaP G) (e a).2)

def scal (θ : InfFam D) (ξ : Module.Dual ℂ (VV ℂ (LaP G))) (Ψ : GLf G → WtSp G) (h : GA D (Xp G)) : ℂ :=
  ξ (rhoK (LaP G) (invTrK (GlobalTheory.CoefModel.realGL θ (Xp G) h⁻¹))
    (GlobalTheory.CoefModel.mapVV D.what₂.embLL (LaP G) (Ψ (Formalism.IndefR.Lev.finE (Xp G) h))))

theorem psi_left (rp : ClassReps G) {n : ℕ} (e : Fin n ≃ TestIx G × VVIdx (LaP G)) (a : Fin n) (γ : UR D.sp.cm (Xp G).gram)
    (g : GLf G) : psi rp e a (ratIn G γ * g) = rhoW G γ (psi rp e a g) := deltaForm_left _ _ _ _ _ _ _

theorem psi_right (rp : ClassReps G) {n : ℕ} (e : Fin n ≃ TestIx G × VVIdx (LaP G)) (a : Fin n) (g : GLf G) {k : GLf G}
    (hk : k ∈ G.Kplus) : psi rp e a (g * k) = psi rp e a g := deltaForm_right _ _ _ _ _ _ hk

open Classical in

theorem ClassReps.gridClassReps_delta_apply_rep (rp : ClassReps G) (hN : rp.Neat) (c c' : G.ClPlus) (v : WtSp G) :
    rp.delta c v (rp.x c') = if c' = c then v else 0 := by
  split_ifs with h
  · subst h; exact deltaForm_self _ _ _ _ _ (hN c')
  · refine deltaForm_eq_zero _ _ _ _ _ _ fun γ u hu he => h ?_
    have hγ : ratIn G γ ∈ UA D.sp.cm (Xp G).gram := by
      have e : ratIn G γ = rp.x c' * u⁻¹ * (rp.x c : GLf G)⁻¹ := by rw [he]; group
      rw [e]
      exact mul_mem (mul_mem (rp.x c').2 (inv_mem hu.1)) (inv_mem (rp.x c).2)
    rw [← rp.classRepresentative_mk c, ← rp.classRepresentative_mk c']
    symm
    exact (DoubleCoset.eq _ _ _ _).2 ⟨⟨_, hγ⟩, ⟨γ.1, γ.2, rfl⟩, ⟨u, hu.1⟩, hu, Subtype.ext he⟩

theorem testFunction_value_at_rep (rp : ClassReps G) (hN : rp.Neat) {n : ℕ} (e : Fin n ≃ TestIx G × VVIdx (LaP G)) (a : Fin n) (c : G.ClPlus) :
    psi rp e a (rp.x c) = valAt (LaP G) e (datumOf e a, c) (Pi.single a 1) := by
  classical
  rw [psi, rp.gridClassReps_delta_apply_rep hN]
  apply (bVV D.what₂.LL (LaP G)).equivFun.injective
  funext i
  have e1 : (bVV D.what₂.LL (LaP G)).equivFun (valAt (LaP G) e (datumOf e a, c) (Pi.single a 1)) i =
      (Pi.single a 1 : Fin n → D.what₂.LL) (e.symm ((datumOf e a, c), i)) := by
    exact congrFun ((bVV D.what₂.LL (LaP G)).equivFun.apply_symm_apply _) i
  have e2 : e.symm ((datumOf e a, c), i) = a ↔ c = (e a).1.2 ∧ i = (e a).2 := by
    rw [Equiv.symm_apply_eq]
    simp [Prod.ext_iff, datumOf]
  rw [e1, Pi.single_apply]
  simp only [e2]
  split_ifs with h1 h2 h2
  · simp [h2.2]
  · have : ¬ (e a).2 = i := fun h => h2 ⟨h1, h.symm⟩
    simp [Finsupp.single_apply, this]
  · exact absurd h2.1 h1
  · simp

variable (G)

theorem posDef_Xp (φ : D.host.E →+* ℂ) : ((Xp G).gram.map φ).PosDef := by
  have := (isV_Xp G).sigOK φ
  rw [(isV_Xp G).sig φ] at this
  exact GlobalTheory.DefiniteQuotient.posDef_of_signature this

theorem isSelfDualE_latOf (g : UA D.sp.cm (Xp G).gram) :
    IsSelfDualE (D.sp.cm.sig : D.host.E →+* D.host.E) (Xp G).gram (latOf G g) := by
  obtain ⟨h1, h2⟩ := (isV_Xp G).sd
  have hf := Module.Finite.iff_fg.2 h1.fg
  exact ⟨Formalism.UG.P.global_lattice_isLattice_holds _ _ _ _ hf h1.span_eq_top _,
    GlobalTheory.PointLattice.globLat_selfDual D.sp.cm.sig _ _ h2 hf h1.span_eq_top g.1 g.2⟩

theorem star_emb (τ : D.what₂.Tau) (x : D.host.E) :
    star (emb D τ x) = emb D τ ((D.sp.cm.sig : D.host.E →+* D.host.E) x) := by
  apply D.what₂.embLL.injective
  rw [D.starLL_cx]
  exact (D.sp.cm.cmUnram.2.1 (D.what₂.embLL.comp (emb D τ)) x).symm

theorem exists_isTestLat (rp : ClassReps G) (n : ℕ) (e : Fin n ≃ TestIx G × VVIdx (LaP G)) : ∃ X' M, IsTestLat G rp n e X' M := by
  obtain ⟨i⟩ := SlopeModel.nonempty_idx (LaP G)
  haveI : Finite (TestIx G) := Finite.of_injective (fun c => e.symm (c, i)) fun _ _ h => congrArg Prod.fst (e.symm.injective h)
  obtain ⟨X, hX⟩ := (SlopeModel.exists_isMetric (formGram G e) fun φ => SlopeModel.sumGram_posDef _ e _ φ fun τ => by
    have hP := posDef_Xp G (φ.comp (emb D τ))
    have hd : IsUnit ((Xp G).gram.map (emb D τ)).det := by
      have := (Matrix.isUnit_iff_isUnit_det _).1 hP.isUnit
      rw [RingHom.coe_comp, ← Matrix.map_map, ← RingHom.mapMatrix_apply φ, ← RingHom.map_det, isUnit_iff_ne_zero,
        map_ne_zero] at this
      exact isUnit_iff_ne_zero.2 this
    have e : (((Xp G).gram.map (emb D τ))⁻¹).map φ = ((Xp G).gram.map (φ.comp (emb D τ)))⁻¹ := by
      symm
      apply Matrix.inv_eq_left_inv
      rw [RingHom.coe_comp, ← Matrix.map_map, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hd,
        Matrix.map_one _ (map_zero _) (map_one _)]
    rw [gramKd, Matrix.transpose_map, e]
    exact hP.inv.transpose).2
  exact ⟨X, _, hX, rfl⟩

variable {G}

theorem IsTestLat.gridTestLattice_largestSlope_bound (hS : SlopeE) {v₀ : InfinitePlace D.what₂.LL} (hv : Formalism.DivisionValues.IsConjAt v₀) {R : ℝ} (hR : 1 ≤ R)
    (hLa : SpreadLe (LaP G) R) {rp : ClassReps G} {n : ℕ} {e : Fin n ≃ TestIx G × VVIdx (LaP G)}
    {X' : InfinitePlace D.what₂.LL → Matrix (Fin n) (Fin n) ℂ} {M : Submodule (𝓞 D.what₂.LL) (Fin n → D.what₂.LL)}
    (h : IsTestLat G rp n e X' M) :
    Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts.TestLatticeCondition n X' M (bound (Fintype.card D.what₂.Tau) (Xp G).rank R) := by
  haveI : Nonempty (TestIx G) := ⟨⟨fun _ => default, Quotient.mk'' 1⟩⟩
  rw [h.2]
  exact (hS D.host.E D.what₂.LL v₀ hv _ (fun φ x => D.sp.cm.cmUnram.2.1 φ x) _ (emb D) star_emb _ (LaP G) R hR hLa
    _ (posDef_Xp G) (TestIx G) (fun c => rp.lat c.2) (fun c => isSelfDualE_latOf G _) n e X').2.2.1 h.1

example : deltaForm (MonoidHom.id ℚˣ) ⊥ ((Algebra.lsmul ℚ ℚ ℚ).toMonoidHom.comp (Units.coeHom ℚ)) 1 (3 : ℚ) (-1) = -3 := by
  have h := deltaForm_left (MonoidHom.id ℚˣ) ⊥ ((Algebra.lsmul ℚ ℚ ℚ).toMonoidHom.comp (Units.coeHom ℚ)) 1 (3 : ℚ) (-1) 1
  rw [deltaForm_self _ _ _ _ _ (by simp)] at h
  simpa using h

end GlobalTheory.FunObj

end
