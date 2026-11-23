import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NumberFieldLatticeDeterminedByLocalLatticesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueGlobalLatticeOfLocalLatticesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproxStabStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordinateLatticeUniqueTermAlmostAllPlacesStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.GlobalOrbits

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {A : Places F E sig} {r k : ℕ}

theorem mem_rat {n : ℕ}
    {K : ∀ p, Subgroup ((Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep))}
    {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} (hg : g ∈ A.rat K) : ∀ p, ∃ g' ∈ K p, A.Ext p g g' := hg

theorem lrel_equivalence (G : GFrames A r k) : Equivalence G.LRel := by
  refine ⟨fun Λ => ⟨1, G.St.one_mem, ?_⟩, ?_, ?_⟩
  · ext x; simp
  · rintro Λ Λ' ⟨g, hg, rfl⟩
    refine ⟨g⁻¹, G.St.inv_mem hg, ?_⟩
    rw [← Submodule.map_comp]
    ext x; simp
  · rintro a b c ⟨g, hg, rfl⟩ ⟨g2, hg2, rfl⟩
    refine ⟨g2 * g, G.St.mul_mem hg2 hg, ?_⟩
    rw [← Submodule.map_comp]
    rfl

theorem drel_equivalence (G : GFrames A r k) : Equivalence G.DRel := by
  refine ⟨fun d => ⟨1, fun p => ⟨1, (G.S p).H0.one_mem, fun _ => rfl, one_smul _ _⟩⟩, ?_, ?_⟩
  · rintro d d' ⟨g, hg⟩
    refine ⟨g⁻¹, fun p => ?_⟩
    obtain ⟨g', h0, he, hd⟩ := hg p
    refine ⟨g'⁻¹, (G.S p).H0.inv_mem h0, fun x => ?_, ?_⟩
    · have h := he (g.symm x)
      rw [LinearEquiv.apply_symm_apply] at h
      change g'.symm (A.bc p x) = A.bc p (g.symm x)
      rw [← h, LinearEquiv.symm_apply_apply]
    · rw [← hd, inv_smul_smul]
  · rintro a b c ⟨g, hg⟩ ⟨g2, hg2⟩
    refine ⟨g2 * g, fun p => ?_⟩
    obtain ⟨g', h0, he, hd⟩ := hg p
    obtain ⟨g2', h20, he2, hd2⟩ := hg2 p
    refine ⟨g2' * g', (G.S p).H0.mul_mem h20 h0, fun x => ?_, ?_⟩
    · change g2' (g' (A.bc p x)) = A.bc p (g2 (g x))
      rw [he x, he2 (g x)]
    · rw [mul_smul, hd, hd2]

theorem local_of_lrel (G : GFrames A r k) {Γ Γ' : G.Lt} (h : G.LRel Γ Γ') :
    ∀ p, ∃ h ∈ (G.S p).St, A.lat p Γ' = h • A.lat p Γ := by
  obtain ⟨g, hg, rfl⟩ := h
  intro p
  obtain ⟨g', hg', he⟩ := mem_rat hg p
  exact ⟨g', hg', (RatExt.rational_extend A _ p).2.2.2.1 g g' Γ he⟩

end GlobalTheory.HL.GlobalOrbits

namespace GlobalTheory.HL.GlobalOrbits

theorem smul_eq_of_le {F' E' : Type} [Field F'] [ValuativeRel F'] [TopologicalSpace F'] [CommRing E']
    [Algebra F' E'] [TopologicalSpace E'] (L : LocE F' E') {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E')
    (Λ : Submodule L.O (Fin n → E')) (hΛ : IsSD L Hm Λ) (u : (Fin n → E') ≃ₗ[E'] (Fin n → E'))
    (hu : u ∈ isomG L Hm) (hle : ∀ x ∈ Λ, u x ∈ Λ) : u • Λ = Λ := by
  have hu' : ∀ x y, hf L Hm (u x) (u y) = hf L Hm x y := hu
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
    exact hle x hx
  · intro hy
    have h1 : u.symm y ∈ Λ := by
      refine (hΛ.2 _).1 fun x hx => ?_
      have := hu' x (u.symm y)
      rw [LinearEquiv.apply_symm_apply] at this
      rw [← this]
      exact (hΛ.2 y).2 hy (u x) (hle x hx)
    have h2 : y = u • u.symm y := by simp
    rw [h2]
    exact Submodule.smul_mem_pointwise_smul _ _ _ h1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {A : Places F E sig} {r k : ℕ}

theorem lrel_of_local (G : GFrames A r k) {d : G.Dat} {Γ Γ' : G.Lt} (hT : G.IsTerm d Γ)
    (hL' : Submodule.IsLattice E Γ') (H : ∀ p, ∃ h ∈ (G.S p).St, A.lat p Γ' = h • A.lat p Γ) :
    G.LRel Γ Γ' := by
  have recΓ := GlobalTheory.T.numberField_lattice_determined_by_local_lattices A _ Γ hT.1
  have recΓ' := GlobalTheory.T.numberField_lattice_determined_by_local_lattices A _ Γ' hL'
  let n : ∀ p, (G.S p).GLV := fun p => if A.lat p Γ' = A.lat p Γ then 1 else (H p).choose
  have hn : ∀ p, n p ∈ (G.S p).St ∧ A.lat p Γ' = n p • A.lat p Γ := by
    intro p
    by_cases hp : A.lat p Γ' = A.lat p Γ
    · simp only [n, if_pos hp]; exact ⟨(G.S p).St.one_mem, by rw [one_smul]; exact hp⟩
    · simp only [n, if_neg hp]; exact (H p).choose_spec
  have hfin : {p | n p ∉ (G.S p).K0}.Finite := by
    refine (recΓ.2.2.union recΓ'.2.2).subset fun p hp => ?_
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
    apply hp
    have : A.lat p Γ' = A.lat p Γ := by rw [hc.1, hc.2]
    simp only [n, if_pos this]
    exact (G.S p).K0.one_mem
  have hc : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ,
      ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = (((fun _ => 1 : ∀ p, ((A.loc p).Fp)ˣ) p) : (A.loc p).Fp)}.Finite :=
    Set.finite_empty.subset fun p hp => hp ⟨1, by simp⟩
  obtain ⟨g, hg, hgp⟩ := GlobalTheory.T.exists_mem_St_approximating_local_elements A r k G Γ hT.1 (fun _ => 1) hc n (fun p => (hn p).1) hfin
  have hloc : ∀ p, A.lat p Γ' = A.lat p (Γ.map ((g : G.V →ₗ[E] G.V).restrictScalars (𝓞 E))) := by
    intro p
    haveI := (A.loc p).lf
    haveI := (A.loc p).char0
    obtain ⟨g', hg'St, he⟩ := mem_rat hg p
    obtain ⟨-, hsub⟩ := hgp p g' he
    have hSD := (TermBasic.term_basic _ _ _ _ _ _ (hT.2 p)).1
    have hmem : (n p)⁻¹ * g' ∈ (G.S p).St := (G.S p).St.mul_mem ((G.S p).St.inv_mem (hn p).1) hg'St
    have hu : (n p)⁻¹ * g' ∈ isomG (A.L p) (G.S p).Hm :=
      (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hmem).1).1).1
    have hle : ∀ x ∈ A.lat p Γ, ((n p)⁻¹ * g') x ∈ A.lat p Γ := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := hsub x hx
      have h2 : ((n p)⁻¹ * g') x = x + y := by
        have h3 : (n p).symm (g' x) = ((n p)⁻¹ * g') x := rfl
        rw [← h3, ← sub_eq_iff_eq_add', hxy]
        simp
      rw [h2]
      exact add_mem hx hy
    have hst := smul_eq_of_le (A.L p) _ _ hSD _ hu hle
    rw [(RatExt.rational_extend A _ p).2.2.2.1 g g' Γ he, (hn p).2]
    rw [show g' • A.lat p Γ = n p • (((n p)⁻¹ * g') • A.lat p Γ) by
      rw [← mul_smul, mul_inv_cancel_left], hst]
  refine ⟨g, hg, le_antisymm ?_ ?_⟩
  · intro x hx
    refine (recΓ'.1 x).2 fun p => ?_
    rw [hloc p]
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  · intro x hx
    have hx' := (recΓ'.1 x).1 hx
    refine ⟨g.symm x, (recΓ.1 _).2 fun p => ?_, by simp⟩
    obtain ⟨g', -, he⟩ := mem_rat hg p
    have h1 := hx' p
    rw [hloc p, (RatExt.rational_extend A _ p).2.2.2.1 g g' Γ he] at h1
    have h2 : A.bc p x = g' • A.bc p (g.symm x) := by
      change _ = g' (A.bc p (g.symm x))
      rw [he, LinearEquiv.apply_symm_apply]
    rw [h2] at h1
    obtain ⟨y, hy, hy'⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h1
    rw [smul_left_cancel_iff] at hy'
    exact hy' ▸ hy

end GlobalTheory.HL.GlobalOrbits

namespace GlobalTheory.HL.GlobalOrbits

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {A : Places F E sig} {r k : ℕ}

theorem glue_terms (G : GFrames A r k) (hk : 4 * r + 7 ≤ k) {d : G.Dat} {Λ₀ : G.Lt}
    (h₀ : G.IsTerm d Λ₀) (Λ : ∀ p, Submodule (A.L p).O (G.S p).V)
    (hΛ : ∀ p, (G.S p).IsTerm (d p) (Λ p)) :
    ∃ Γ, G.IsTerm d Γ ∧ ∀ p, ∃ h ∈ (G.S p).St, A.lat p Γ = h • Λ p := by
  have hstd := GlobalTheory.T.coordinateLattice_unique_term_almost_all_places A r k G hk
  have rec₀ := GlobalTheory.T.numberField_lattice_determined_by_local_lattices A _ Λ₀ h₀.1
  obtain ⟨B, hBfin, hB⟩ : ∃ B : Set (HeightOneSpectrum (𝓞 F)), B.Finite ∧ ∀ p ∉ B,
      A.lat p Λ₀ = Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V)) ∧
      ∃ h ∈ (G.S p).St, Λ p = h • Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V)) := by
    refine ⟨_, hstd.union rec₀.2.2, fun p hp => ?_⟩
    haveI := (A.loc p).lf
    haveI := (A.loc p).char0
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hp
    obtain ⟨⟨-, -, -, d₀, hW, -, -, hT1, -, -⟩, hl⟩ := hp
    have hTp : (G.S p).IsTerm (d p) (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V))) := by
      rw [← hl]; exact h₀.2 p
    have hd : d₀ = d p :=
      (TermBasic.term_basic _ _ _ _ _ _ hTp).2.2.2.2.2.2.2 d₀ ⟨(1, 1), hW⟩
    refine ⟨hl, hT1 (Λ p) ?_⟩
    rw [hd]; exact hΛ p
  let Λ' : ∀ p, Submodule (A.L p).O (G.S p).V := fun p => if p ∈ B then Λ p else
    Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V))
  have hterm : ∀ p, (G.S p).IsTerm (d p) (Λ' p) := by
    intro p
    by_cases hp : p ∈ B
    · simp only [Λ', if_pos hp]; exact hΛ p
    · simp only [Λ', if_neg hp]; rw [← (hB p hp).1]; exact h₀.2 p
  have hlat : ∀ p, IsLat (A.L p) (Λ' p) := by
    intro p
    haveI := (A.loc p).lf
    haveI := (A.loc p).char0
    exact (TermBasic.term_basic _ _ _ _ _ _ (hterm p)).1.1
  have hfin : {p | Λ' p ≠ Submodule.span (A.L p).O
      (Set.range fun i => (Pi.single i 1 : Fin (k + 2 * r + 1) → (A.loc p).Ep))}.Finite := by
    refine hBfin.subset fun p hp => ?_
    by_contra hc
    apply hp
    simp only [Λ', if_neg hc]
  obtain ⟨Γ, ⟨hL, hlatΓ⟩, -⟩ := GlobalTheory.T.exists_unique_global_lattice_of_local_lattices A _ Λ' hlat hfin
  refine ⟨Γ, ⟨hL, fun p => (hlatΓ p).symm ▸ hterm p⟩, fun p => ?_⟩
  by_cases hp : p ∈ B
  · refine ⟨1, (G.S p).St.one_mem, ?_⟩
    rw [hlatΓ p, one_smul]
    simp only [Λ', if_pos hp]
  · obtain ⟨h, hh, he⟩ := (hB p hp).2
    refine ⟨h⁻¹, (G.S p).St.inv_mem hh, ?_⟩
    rw [hlatΓ p, he, inv_smul_smul]
    simp only [Λ', if_neg hp]

end GlobalTheory.HL.GlobalOrbits

open GlobalTheory.HL.GlobalOrbits in

theorem GlobalTheory.HL.GlobalOrbits.global_terms_orbits : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → ∀ d : G.Dat, (∃ Λ₀, G.IsTerm d Λ₀) → (∀ Λ : ∀ p, Submodule (A.L p).O (G.S p).V, (∀ p, (G.S p).IsTerm (d p) (Λ p)) → ∃ Γ, G.IsTerm d Γ ∧ ∀ p, ∃ h ∈ (G.S p).St, A.lat p Γ = h • Λ p) ∧ (∀ Γ Γ', G.IsTerm d Γ → Submodule.IsLattice E Γ' → (G.LRel Γ Γ' ↔ ∀ p, ∃ h ∈ (G.S p).St, A.lat p Γ' = h • A.lat p Γ)) ∧ Equivalence G.LRel ∧ Equivalence G.DRel := by
  intro F E _ _ _ _ _ sig A r k G hk d hex
  obtain ⟨Λ₀, h₀⟩ := hex
  exact ⟨fun Λ hΛ => glue_terms G hk h₀ Λ hΛ,
    fun Γ Γ' hT hL' => ⟨fun h => local_of_lrel G h, fun H => lrel_of_local G hT hL' H⟩,
    lrel_equivalence G, drel_equivalence G⟩
