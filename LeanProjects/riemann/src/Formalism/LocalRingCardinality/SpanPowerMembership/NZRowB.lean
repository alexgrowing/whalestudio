import Formalism.LocalRingCardinality.DataAmbForm
import Formalism.LocalRingCardinality.DataKap
import Formalism.LocalRingCardinality.DataDIVDefs
import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowA

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions

section Gen

variable {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
  [FiniteDimensional ℂ EE] (S : RowSide D EE)

theorem baseSubspace_top_of_identity {μ} (he : S.eOp μ = LinearMap.id) : S.V0 μ = ⊤ := by
  unfold RowSide.V0; rw [he]; exact LinearMap.range_id

theorem Usp_bot {μ} (he : S.eOp μ = LinearMap.id) (hi : Function.Injective (S.iota μ)) : S.Usp μ = ⊥ := by
  unfold RowSide.Usp; rw [baseSubspace_top_of_identity S he, LinearMap.ker_eq_bot.mpr hi, inf_bot_eq]

theorem Qsp_top {μ} (he : S.eOp μ = LinearMap.id) (hi : Function.Injective (S.iota μ)) : S.Qsp μ = ⊤ := by
  unfold RowSide.Qsp; rw [baseSubspace_top_of_identity S he, Usp_bot S he hi, Submodule.bot_orthogonal_eq_top, inf_top_eq]

theorem LamSet_eq {μ} (he : S.eOp μ = LinearMap.id) (hi : Function.Injective (S.iota μ)) :
    S.LamSet μ = (S.Mtilde μ).carrier := by
  unfold RowSide.LamSet
  have hp : ∀ x, (S.Qsp μ).starProjection x = x := fun x =>
    Submodule.starProjection_eq_self_iff.mpr (by rw [Qsp_top S he hi]; trivial)
  rw [baseSubspace_top_of_identity S he]
  ext x
  simp [hp]

theorem RRset_eq {μ} (he : S.eOp μ = LinearMap.id) (hi : Function.Injective (S.iota μ)) :
    S.RRset μ = S.iota μ '' (S.Mtilde μ).carrier := by
  unfold RowSide.RRset; rw [LamSet_eq S he hi]

theorem rrDef_of (Λ : Submodule (𝓞 D.what₂.LL) S.RR.V)
    (h : ∀ w y, S.jEE y ∈ S.RRset (D.what₂.muAt w) ↔ y ∈ Λ) (hL : S.RR.L = Λ) : S.RRDef := by
  intro x
  have hs : ∀ w, Submodule.span (𝓞 D.what₂.LL) {y | S.jEE y ∈ S.RRset (D.what₂.muAt w)} = Λ := fun w => by
    have : {y | S.jEE y ∈ S.RRset (D.what₂.muAt w)} = (Λ : Set S.RR.V) := Set.ext fun y => h w y
    rw [this, Submodule.span_eq]
  rw [hL]
  constructor
  · intro hx w
    exact ⟨1, fun h1 => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1), by
      rw [one_smul, hs]; exact hx⟩
  · intro hx
    refine mem_of_local Λ x fun P hP => ?_
    have hne : P ≠ ⊥ := fun hb => RingOfIntegers.not_isField D.what₂.LL
      (Ring.isField_iff_maximal_bot.mpr (hb ▸ hP))
    obtain ⟨d, hd, hdx⟩ := hx (D.plEq.symm ⟨P, hP.isPrime, hne⟩)
    rw [hs] at hdx
    rw [Equiv.apply_symm_apply] at hd
    exact ⟨d, hd, hdx⟩

end Gen

structure CentralCharacterOne (D : D7) where
  χ : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) →ₐ[ℂ] ℂ
  cen : D.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))
  one : χ ⟨D.ntypes.e0, cen⟩ = 1

section Std

variable (D : D7) (c : CentralCharacterOne D) {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
  [FiniteDimensional ℂ EE] {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ EE)

def stdSide : RowSide D EE where
  Amb := fun _ => EE
  Mult := fun _ _ => EE
  multZero := fun _ => LinearIsometryEquiv.refl ℂ EE
  multTop := fun _ => LinearIsometryEquiv.refl ℂ EE
  io := fun _ _ => LinearMap.id
  Mtilde := fun _ => oB b _
  cen := fun _ => (Algebra.ofId ℂ (Module.End ℂ EE)).comp c.χ
  eOp := fun _ => LinearMap.id
  eOp_idem := fun _ => rfl
  eOp_sa := fun _ _ _ => rfl
  eOp_tie := fun _ => by
    rw [dif_pos c.cen]
    show LinearMap.id = algebraMap ℂ (Module.End ℂ EE) (c.χ ⟨D.ntypes.e0, c.cen⟩)
    rw [c.one, map_one]; rfl
  RR := stdH D.what₂.LL n
  RR_frames := stdH_frames _ n
  jEE := jB D.what₂.embLL b
  jEE_basis := jB_basis _ b
  jEE_norm := jB_norm _ b

theorem stdSide_downTo (μ) (j : ℕ) : (stdSide D c b).downTo μ j = LinearMap.id := by
  induction j with
  | zero => rfl
  | succ j ih => show ((stdSide D c b).downTo μ j).comp LinearMap.id = _; rw [ih]; rfl

theorem stdSide_iota (μ) : (stdSide D c b).iota μ = LinearMap.id := by
  show (LinearMap.id : EE →ₗ[ℂ] EE) ∘ₗ (stdSide D c b).downTo μ D.R.m ∘ₗ (LinearMap.id : EE →ₗ[ℂ] EE) = _
  rw [stdSide_downTo]; rfl

end Std

theorem jB_mem_oB {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) {n : ℕ}
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (b : OrthonormalBasis (Fin n) ℂ V)
    {O : Type} [CommRing O] (f : O →+* K) (hf : ∀ z : K, (∃ y, f y = z) ↔ ∃ c : 𝓞 K, z = (c : K))
    (x : Fin n → K) : jB σ b x ∈ (oB b (σ.comp f)).carrier ↔ x ∈ (stdH K n).L := by
  rw [mem_oB, mem_stdL]
  constructor
  · rintro ⟨c, hc⟩ i
    refine (hf (x i)).mp ⟨c i, σ.injective ?_⟩
    have h2 : (∑ k, (σ.comp f) (c k) • b k) = jB σ b (fun k => f (c k)) := rfl
    have h1 := congrArg (fun y => b.repr y i) hc
    simp only [h2, repr_jB] at h1
    exact h1.symm
  · intro h
    have h' := fun i => (hf (x i)).mpr (h i)
    choose c hc using h'
    exact ⟨c, by rw [jB_apply]; exact Finset.sum_congr rfl fun i _ => by rw [RingHom.comp_apply, hc i]⟩

def OFull (D : D7) : Prop := ∀ z : D.what₂.LL, (∃ y, D.what₂.OtoLL y = z) ↔ ∃ c : 𝓞 D.what₂.LL, z = (c : D.what₂.LL)

section Std2

variable (D : D7) (c : CentralCharacterOne D) (hO : OFull D) {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
  [FiniteDimensional ℂ EE] {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ EE)

include hO in
theorem stdSide_rrDef : (stdSide D c b).RRDef := by
  refine rrDef_of _ (stdH D.what₂.LL n).L (fun w y => ?_) rfl
  rw [RRset_eq _ rfl (by rw [stdSide_iota]; exact Function.injective_id), stdSide_iota]
  have e : (⇑(LinearMap.id : EE →ₗ[ℂ] EE)) '' ((stdSide D c b).Mtilde (D.what₂.muAt w)).carrier =
      (oB b (D.what₂.embLL.comp D.what₂.OtoLL)).carrier := Set.image_id _
  exact (iff_of_eq (congrArg (fun s => jB D.what₂.embLL b y ∈ s) e)).trans
    (jB_mem_oB D.what₂.embLL b D.what₂.OtoLL hO y)

theorem stdSide_rrFull : (stdSide D c b).RRFull := (stdH_good D.what₂.LL n).2

def ambOf (S : RowSide D EE) (m : D.what₂.Tup → ℕ) (bA : ∀ μ, OrthonormalBasis (Fin (m μ)) ℂ (S.Amb μ))
    (hg : ∀ μ, (S.Mtilde μ).gen = genB (bA μ)) : AmbForm D S where
  MtH := fun μ => stdH D.what₂.LL (m μ)
  jAmb := fun μ => jB D.what₂.embLL (bA μ)
  MtH_good := fun μ _ => stdH_good _ _
  jAmb_basis := fun μ _ => jB_basis _ _
  jAmb_lat := fun μ _ x => by rw [hg]; exact jB_lat _ _ x
  jAmb_gen := fun μ _ => by rw [hg]; exact jB_gen _ _
  jAmb_norm := fun μ _ => jB_norm _ _

def standardBaseSide : BaseLevelRowSide D := ⟨stdSide D c D.what₂.onb0⟩

include hO in
theorem standardBaseSide_latticeDefined : (standardBaseSide D c).s.RRDef := stdSide_rrDef D c hO _

def standardAmbientForm : AmbForm D (standardBaseSide D c).s := ambOf D _ (fun _ => D.what₂.D0) (fun _ => D.what₂.onb0) (fun _ => rfl)

end Std2

end Formalism.BasicNotions.Examples₂.NZ
