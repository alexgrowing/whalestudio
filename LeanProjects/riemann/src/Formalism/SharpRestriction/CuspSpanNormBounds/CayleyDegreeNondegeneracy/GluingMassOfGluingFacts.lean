import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.CardOrbitMulCardStabilizer
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.LatLiftIndep
import Formalism.HermitianLattices.FinalNeighbourConstruct

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence.LatticeLiftIndependence

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Dat

variable (D : D7)

abbrev SumWLine : Type := (D.sp.X 0).V × D.host.E

def embedWithZ {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) : SumWLine D →ₗ[D.host.E] (VS D).V :=
  (D.sp.iXY 0).coprod (LinearMap.toSpanSingleton D.host.E (VS D).V F0.z)

def latticeWithZ {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : LatV D) : Submodule (𝓞 D.host.E) (SumWLine D) :=
  (Lsub Λ (lf D F0)).comap ((embedWithZ D F0).restrictScalars (𝓞 D.host.E))

def extendByOne (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) : SumWLine D ≃ₗ[D.host.E] SumWLine D :=
  γ.prodCongr (LinearEquiv.refl D.host.E D.host.E)

def intersectFirstSummand (𝓛 : Submodule (𝓞 D.host.E) (SumWLine D)) : Submodule (𝓞 D.host.E) (D.sp.X 0).V :=
  𝓛.comap ((LinearMap.inl D.host.E (D.sp.X 0).V D.host.E).restrictScalars (𝓞 D.host.E))

theorem extendByOne_one : extendByOne D 1 = 1 := by
  apply LinearEquiv.ext
  rintro ⟨w, c⟩
  rfl

theorem extendByOne_mul (a b : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) :
    extendByOne D (a * b) = extendByOne D a * extendByOne D b := by
  apply LinearEquiv.ext
  rintro ⟨w, c⟩
  rfl

@[instance_reducible] def unitaryActOnLatticesWLine : MulAction (isom (D.sp.X 0).hT) (Submodule (𝓞 D.host.E) (SumWLine D)) where
  smul γ 𝓛 := gmap (extendByOne D γ.1) 𝓛
  one_smul 𝓛 := by
    change gmap (extendByOne D 1) 𝓛 = 𝓛
    rw [extendByOne_one, gmap_one]
  mul_smul a b 𝓛 := by
    change gmap (extendByOne D (a.1 * b.1)) 𝓛 = gmap (extendByOne D a.1) (gmap (extendByOne D b.1) 𝓛)
    rw [extendByOne_mul, gmap_mul]

@[instance_reducible] def unitaryActOnLatticesW : MulAction (isom (D.sp.X 0).hT) (Submodule (𝓞 D.host.E) (D.sp.X 0).V) where
  smul γ M := gmap γ.1 M
  one_smul M := gmap_one M
  mul_smul a b M := gmap_mul a.1 b.1 M

theorem partInW_gmap_extendByOne (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) (𝓛 : Submodule (𝓞 D.host.E) (SumWLine D)) :
    intersectFirstSummand D (gmap (extendByOne D γ) 𝓛) = gmap γ (intersectFirstSummand D 𝓛) := by
  ext w
  rw [isomAct_mem_gmap]
  unfold intersectFirstSummand
  rw [Submodule.mem_comap, Submodule.mem_comap, isomAct_mem_gmap]
  rfl

theorem z_orth_embedding (u : D.what₂.Word) (w : (D.sp.X 0).V) : (VS D).hT (D.zmOf u) (D.sp.iXY 0 w) = 0 := by
  have h1 : (VS D).hT D.sp.zm (D.sp.iXY 0 w) = 0 := by
    rw [← (VS D).herm.eq (D.sp.iXY 0 w) D.sp.zm, D.sp.zm_orth w, map_zero]
  unfold D7.zmOf
  rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, h1, smul_zero]

theorem partInW_latticeWithZ (u : D.what₂.Word) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (hz : F0.z = D.zmOf u) (Λ : LatV D) :
    intersectFirstSummand D (latticeWithZ D F0 Λ) = L0X D Λ (lf D F0) := by
  ext w
  unfold intersectFirstSummand latticeWithZ L0X L0sub
  simp only [Submodule.mem_comap, Submodule.mem_inf, LinearMap.restrictScalars_apply]
  have e : embedWithZ D F0 (LinearMap.inl D.host.E (D.sp.X 0).V D.host.E w) = D.sp.iXY 0 w := by
    simp [embedWithZ]
  rw [e]
  constructor
  · intro h
    refine ⟨h, ?_⟩
    change (VS D).hT F0.z (D.sp.iXY 0 w) = 0
    rw [hz]
    exact z_orth_embedding D u w
  · exact fun h => h.1

end Dat

section Glue

open Classical

def ForPrimeFlag (D : D7) (u : D.what₂.Word)
    (Q : (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) → Prop) : Prop :=
  (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → Q F0

def LatticeClassesIff (D : D7) (u : D.what₂.Word) : Prop :=
  ForPrimeFlag D u fun F0 => ∀ Λ₁ Λ₂ : LatV D, IsRowLat D F0 Λ₁ → IsRowLat D F0 Λ₂ →
    ((∃ σ ∈ stabF D F0, gmap σ Λ₁ = Λ₂) ↔
      ∃ γ ∈ isom (D.sp.X 0).hT, gmap (extendByOne D γ) (latticeWithZ D F0 Λ₁) = latticeWithZ D F0 Λ₂)

def CardAutEqCardIsometryStabilizer (D : D7) (u : D.what₂.Word) : Prop :=
  ForPrimeFlag D u fun F0 => ∀ Λ : LatV D, IsRowLat D F0 Λ →
    Nat.card (autLz D F0 Λ) =
      Nat.card {γ : isom (D.sp.X 0).hT // gmap (extendByOne D γ.1) (latticeWithZ D F0 Λ) = latticeWithZ D F0 Λ}

def IsometriesTransportLattices (D : D7) (u : D.what₂.Word) : Prop :=
  ForPrimeFlag D u fun F0 => ∀ γ ∈ isom (D.sp.X 0).hT, ∀ Λ₁ : LatV D, IsRowLat D F0 Λ₁ →
    ∃ Λ₂ : LatV D, IsRowLat D F0 Λ₂ ∧ latticeWithZ D F0 Λ₂ = gmap (extendByOne D γ) (latticeWithZ D F0 Λ₁)

def GluingCount (D : D7) (u : D.what₂.Word) : Prop :=
  ForPrimeFlagLattice D u fun F0 Λ => ∀ M ∈ genus (D.sp.X 0).hT (L0X D Λ (lf D F0)),
    {𝓛 | 𝓛 ∈ {𝓛 | ∃ Λ', IsRowLat D F0 Λ' ∧ latticeWithZ D F0 Λ' = 𝓛} ∧ intersectFirstSummand D 𝓛 = M}.Finite ∧
    {𝓛 | 𝓛 ∈ {𝓛 | ∃ Λ', IsRowLat D F0 Λ' ∧ latticeWithZ D F0 Λ' = 𝓛} ∧ intersectFirstSummand D 𝓛 = M}.ncard = (Tu D u - 1) ^ D.R.f

def OrthLatticesOneGenus (D : D7) (u : D.what₂.Word) : Prop :=
  ForPrimeFlagLattice D u fun F0 Λ => ∀ Λ' : LatV D, IsRowLat D F0 Λ' →
    L0X D Λ' (lf D F0) ∈ genus (D.sp.X 0).hT (L0X D Λ (lf D F0))

theorem one_mem_flag_stabilizer (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ stabF D F0 := by
  refine ⟨(isom (VS D).hT).one_mem, fun j => ?_, rfl⟩
  ext x
  simp

theorem fibres_of_gluing_facts (D : D7) (u : D.what₂.Word) (hpos : IsPosDef (D.sp.X 0).hT)
    (h1 : LatticeClassesIff D u) (h2 : CardAutEqCardIsometryStabilizer D u) (h3 : IsometriesTransportLattices D u) (h4 : GluingCount D u)
    (h5 : OrthLatticesOneGenus D u) : FibresOrthLatticeOneGenus D u := by
  intro hT hT3 hsp F0 he hz Λ hΛ s hs
  refine ⟨fun Λ' hΛ' => h5 hT hT3 hsp F0 he hz Λ hΛ Λ' (hs.1 Λ' hΛ'), fun M hM => ?_⟩
  have g1 := h1 hT hT3 hsp F0 he hz
  have g2 := h2 hT hT3 hsp F0 he hz
  have g3 := h3 hT hT3 hsp F0 he hz
  obtain ⟨g4f, g4c⟩ := h4 hT hT3 hsp F0 he hz Λ hΛ M hM
  letI := unitaryActOnLatticesWLine D
  letI := unitaryActOnLatticesW D
  have hinj : Set.InjOn (latticeWithZ D F0) (s : Set (LatV D)) := by
    intro Λ₁ hΛ₁ Λ₂ hΛ₂ heq
    rw [Finset.mem_coe] at hΛ₁ hΛ₂
    obtain ⟨σ, hσ, hσe⟩ := (g1 Λ₁ Λ₂ (hs.1 _ hΛ₁) (hs.1 _ hΛ₂)).2
      ⟨1, (isom (D.sp.X 0).hT).one_mem, by rw [extendByOne_one, gmap_one, heq]⟩
    obtain ⟨Λ₀, _, huniq⟩ := hs.2 Λ₂ (hs.1 _ hΛ₂)
    exact (huniq Λ₁ ⟨hΛ₁, σ, hσ, hσe⟩).trans (huniq Λ₂ ⟨hΛ₂, 1, one_mem_flag_stabilizer D F0, gmap_one _⟩).symm
  have hAfin : Finite (MulAction.stabilizer (isom (D.sp.X 0).hT) M) := by
    have hf := final_autFinite D.host.E (D.sp.X 0).V (D.sp.X 0).hT (D.sp.X 0).herm (trace_inner_self_pos _ hpos) M hM.1
    have := hf.to_subtype
    exact Finite.of_injective
      (fun γ : MulAction.stabilizer (isom (D.sp.X 0).hT) M =>
        (⟨γ.1.1, γ.1.2, γ.2⟩ : {g : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V | g ∈ isom (D.sp.X 0).hT ∧ gmap g M = M}))
      (fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun x => x.1) hab)))
  have key := sum_fibre_inv_card_stabilizer (Γ := isom (D.sp.X 0).hT) (intersectFirstSummand D) (fun γ x => partInW_gmap_extendByOne D γ.1 x)
    {𝓛 | ∃ Λ', IsRowLat D F0 Λ' ∧ latticeWithZ D F0 Λ' = 𝓛}
    (by
      rintro γ _ ⟨Λ₁, hΛ₁, rfl⟩
      obtain ⟨Λ₂, hΛ₂, e⟩ := g3 γ.1 γ.2 Λ₁ hΛ₁
      exact ⟨Λ₂, hΛ₂, e⟩)
    (s.image (latticeWithZ D F0))
    (by
      intro x hx
      obtain ⟨Λ₁, hΛ₁, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨Λ₁, hs.1 _ hΛ₁, rfl⟩)
    (by
      rintro _ ⟨Λ₂, hΛ₂, rfl⟩
      obtain ⟨Λ₀, ⟨hΛ₀, σ, hσ, hσe⟩, huniq⟩ := hs.2 Λ₂ hΛ₂
      obtain ⟨γ, hγ, hγe⟩ := (g1 Λ₀ Λ₂ (hs.1 _ hΛ₀) hΛ₂).1 ⟨σ, hσ, hσe⟩
      refine ⟨latticeWithZ D F0 Λ₀, ⟨Finset.mem_image_of_mem _ hΛ₀, ⟨γ, hγ⟩, hγe⟩, ?_⟩
      rintro y ⟨hy, γ', hγ'⟩
      obtain ⟨Λ₁, hΛ₁, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨σ', hσ', hσe'⟩ := (g1 Λ₁ Λ₂ (hs.1 _ hΛ₁) hΛ₂).2 ⟨γ'.1, γ'.2, hγ'⟩
      rw [huniq Λ₁ ⟨hΛ₁, σ', hσ', hσe'⟩])
    M hAfin g4f
  rw [Finset.filter_image, Finset.sum_image (fun a ha b hb => hinj (Finset.mem_filter.1 ha).1 (Finset.mem_filter.1 hb).1)] at key
  have hcardM : Nat.card (MulAction.stabilizer (isom (D.sp.X 0).hT) M) = Nat.card (Formalism.ThetaLiftIndependence.autL (D.sp.X 0).hT M) :=
    Nat.card_congr
      { toFun := fun γ => ⟨γ.1.1, γ.1.2, γ.2⟩
        invFun := fun g => ⟨⟨g.1, g.2.1⟩, g.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hT1 : 1 ≤ Tu D u := by omega
  rw [g4c, hcardM] at key
  have hfilt : s.filter (fun Λ' => ∃ g ∈ isom (D.sp.X 0).hT, gmap g M = L0X D Λ' (lf D F0)) =
      s.filter (fun Λ' => ∃ γ : isom (D.sp.X 0).hT, γ • M = intersectFirstSummand D (latticeWithZ D F0 Λ')) := by
    refine Finset.filter_congr fun Λ' _ => ?_
    rw [partInW_latticeWithZ D u F0 hz]
    constructor
    · rintro ⟨g, hg, e⟩
      exact ⟨⟨g, hg⟩, e⟩
    · rintro ⟨g, e⟩
      exact ⟨g.1, g.2, e⟩
  rw [hfilt]
  calc _ = ∑ Λ' ∈ s.filter (fun Λ' => ∃ γ : isom (D.sp.X 0).hT, γ • M = intersectFirstSummand D (latticeWithZ D F0 Λ')),
        ((Nat.card (MulAction.stabilizer (isom (D.sp.X 0).hT) (latticeWithZ D F0 Λ')) : ℕ) : ℝ)⁻¹ := by
        refine Finset.sum_congr rfl fun Λ' hΛ' => ?_
        unfold wRow
        rw [g2 Λ' (hs.1 _ (Finset.mem_filter.1 hΛ').1)]
        rfl
    _ = _ := by
        rw [key, div_eq_mul_inv]
        push_cast [Nat.cast_sub hT1]
        rfl

theorem gluing_mass_of_gluing_facts (D : D7) (u : D.what₂.Word) (hpos : IsPosDef (D.sp.X 0).hT)
    (hlat : ForPrimeFlagLattice D u fun F0 Λ => Submodule.IsLattice D.host.E (L0X D Λ (lf D F0)))
    (h1 : LatticeClassesIff D u) (h2 : CardAutEqCardIsometryStabilizer D u) (h3 : IsometriesTransportLattices D u) (h4 : GluingCount D u)
    (h5 : OrthLatticesOneGenus D u) : WordRowsGluing D u :=
  gluing_mass_of_fibre_structure D u hpos hlat (fibres_of_gluing_facts D u hpos h1 h2 h3 h4 h5)

end Glue

end Formalism.MainNotions.BridgeLemma₂

end
