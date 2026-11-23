import Formalism.SharpRestriction.LevelLetterCocycles.RealisedOfCoordArc

noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    [Fintype (K →ₐ[Qp] LL)]

variable (W) in

def EEl (i : ZMod n) : AddSubgroup W.EE where
  carrier := {ε | (letE i : LetA O n) • ε = ε ∧ ∀ δ ∈ W.DelF, W.γE δ ε = ε}
  zero_mem' := ⟨smul_zero _, fun δ _ => map_zero _⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨by rw [smul_add, ha, hb], fun δ hδ => by rw [map_add, ha' δ hδ, hb' δ hδ]⟩
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨by rw [smul_neg, ha], fun δ hδ => by rw [map_neg, ha' δ hδ]⟩

def lc {T : LocLat G Qp LL O} {ι : Type} [Fintype ι] (b : ι → W.DD T) (c : ι → W.EE) : W.DD T :=
  ∑ j, c j • b j

variable (W) in

def LBasis (T : LocLat G Qp LL O) (i : ZMod n) {ι : Type} [Fintype ι] (b : ι → W.DD T) : Prop :=
  (∀ c : ι → W.EE, (∀ j, c j ∈ EEl W i) → lc b c ∈ DDl W T i) ∧
  (∀ c c' : ι → W.EE, (∀ j, c j ∈ EEl W i) → (∀ j, c' j ∈ EEl W i) → lc b c = lc b c' → c = c') ∧
  (∀ x ∈ DDl W T i, ∃ c : ι → W.EE, (∀ j, c j ∈ EEl W i) ∧ lc b c = x)

structure CoeffData (hR : Ring9 W) where
  M : Type
  [acg : AddCommGroup M]
  [mod : Module (PowerSeries O) M]
  κ : ZMod n → M →+ W.EE
  m₁ : M
  mem : ∀ i m, κ i m ∈ EEl W i
  surj : ∀ i, ∀ ε ∈ EEl W i, ∃ m, κ i m = ε
  inj : ∀ i, Function.Injective (κ i)
  semi : ∀ i (a : PowerSeries O) (m : M),
    κ i (a • m) = algebraMap (LetA O n) W.EE ((baseIdOf hR).d a) * κ i m
  unit : ∀ i, κ i m₁ = algebraMap (LetA O n) W.EE (letE i)

attribute [instance] CoeffData.acg CoeffData.mod

def CoeffStep (hR : Ring9 W) : Prop := Nonempty (CoeffData hR)

variable (W) in

def SplitStep : Prop :=
  ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), CrysLat PD T₁ → CrysLat PD T₂ → F.Onto →
    ∃ r k : ℕ, ∀ i : ZMod n, ∃ (b₁ : Fin r ⊕ Fin k → W.DD T₁) (b₂ : Fin r → W.DD T₂),
      LBasis W T₁ i b₁ ∧ LBasis W T₂ i b₂ ∧ (∀ j, W.map F (b₁ (Sum.inl j)) = b₂ j) ∧
        ∀ j, W.map F (b₁ (Sum.inr j)) = 0

variable (W) in

def UnitStep (e : W.DD W.one) : Prop := ∀ i : ZMod n, LBasis W W.one i (fun _ : Unit => e)

section Build

variable {hR : Ring9 W} (D : CoeffData hR) {T : LocLat G Qp LL O} {ι : Type} [Fintype ι]
  (b : ZMod n → ι → W.DD T) (hb : ∀ i, LBasis W T i (b i))

def toL (i : ZMod n) : (ι → D.M) →+ ↥(DDl W T i) where
  toFun c := ⟨lc (b i) (fun j => D.κ i (c j)), (hb i).1 _ (fun j => D.mem i _)⟩
  map_zero' := by
    apply Subtype.ext
    simp [lc]
  map_add' c c' := by
    apply Subtype.ext
    simp [lc, add_smul, Finset.sum_add_distrib]

theorem toL_coe (i : ZMod n) (c : ι → D.M) :
    ((toL D b hb i c : ↥(DDl W T i)) : W.DD T) = lc (b i) (fun j => D.κ i (c j)) := rfl

theorem toL_bij (i : ZMod n) : Function.Bijective (toL D b hb i) := by
  constructor
  · intro c c' h
    have h1 := congrArg Subtype.val h
    rw [toL_coe, toL_coe] at h1
    have h2 := (hb i).2.1 _ _ (fun j => D.mem i _) (fun j => D.mem i _) h1
    funext j
    exact D.inj i (congrFun h2 j)
  · rintro ⟨x, hx⟩
    obtain ⟨c, hc, hcx⟩ := (hb i).2.2 x hx
    choose m hm using fun j => D.surj i (c j) (hc j)
    refine ⟨m, Subtype.ext ?_⟩
    rw [toL_coe]
    change lc (b i) (fun j => D.κ i (m j)) = x
    rw [← hcx]
    congr 1
    funext j
    exact hm j

def coordOf : Coord W (baseIdOf hR) T where
  V := ι → D.M
  θ i := AddEquiv.ofBijective (toL D b hb i) (toL_bij D b hb i)
  θ_smul i a c := by
    change lc (b i) (fun j => D.κ i ((a • c) j)) = (baseIdOf hR).d a • lc (b i) (fun j => D.κ i (c j))
    simp only [lc, Pi.smul_apply, D.semi, Finset.smul_sum, mul_smul, algebraMap_smul]

theorem coordOf_t_apply_eq_sum_kappa_smul (i : ZMod n) (c : ι → D.M) :
    (coordOf D b hb).t i c = ∑ j, D.κ i (c j) • b i j := rfl

end Build

theorem coordSteps_of (hR : Ring9 W) (e : W.DD W.one) (hK : CoeffStep hR) (hS : SplitStep W)
    (hU : UnitStep W e) : CoordSteps hR e := by
  intro T₁ T₂ F hc₁ hc₂ hon
  obtain ⟨D⟩ := hK
  obtain ⟨r, k, hb⟩ := hS T₁ T₂ F hc₁ hc₂ hon
  choose b₁ b₂ h₁ h₂ hin hout using hb
  refine ⟨coordOf D b₁ h₁, coordOf D b₂ h₂,
    coordOf (ι := Unit) D (fun (_ : ZMod n) (_ : Unit) => e) (fun i => hU i),
    { f := LinearMap.funLeft (PowerSeries O) D.M Sum.inl
      coord_hom_map_trace := fun i c => ?_
      crys := hc₁.2.2.2
      crys' := hc₂.2.2.2 }, fun _ => D.m₁, fun i => ?_⟩
  · change ∑ j, D.κ i (c (Sum.inl j)) • b₂ i j = W.map F (∑ j, D.κ i (c j) • b₁ i j)
    rw [map_sum, Fintype.sum_sum_type]
    simp only [map_smul, hin, hout, smul_zero, Finset.sum_const_zero, add_zero]
  · change ∑ _u : Unit, D.κ i D.m₁ • e = (letE i : LetA O n) • e
    rw [Fintype.sum_unique, D.unit, algebraMap_smul]

end Formalism.MainNotions.N.Ln03
