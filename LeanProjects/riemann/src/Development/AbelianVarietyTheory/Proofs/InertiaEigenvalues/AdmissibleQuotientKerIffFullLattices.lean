import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleModuleIffLatticeQuotients

noncomputable section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Polynomial
open Formalism.MainNotions.N (GRep)

namespace GlobalTheory.FullCharpoly

section Lat
variable {G LL O V W : Type} [Group G] [Field LL] [CommRing O] [Algebra O LL]
  [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  [AddCommGroup W] [Module LL W] [Module O W] [IsScalarTower O LL W]
  {ρ : Representation LL G V} {σ : Representation LL G W}

def mapLat (e : V ≃ₗ[LL] W) (he : ∀ g x, e (ρ g x) = σ g (e x)) (L : Lattice (O := O) ρ) :
    Lattice (O := O) σ where
  T := L.T.map ((e.restrictScalars O : V ≃ₗ[O] W) : V →ₗ[O] W)
  stable := by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨ρ g x, L.stable g x hx, he g x⟩
  fg := L.fg.map _
  free := by
    have := L.free
    exact Module.Free.of_equiv ((e.restrictScalars O).submoduleMap L.T)
  span := by
    have h : ((L.T.map ((e.restrictScalars O : V ≃ₗ[O] W) : V →ₗ[O] W) : Submodule O W) : Set W) =
        (e : V →ₗ[LL] W) '' (L.T : Set V) := rfl
    rw [h, Submodule.span_image, L.span, Submodule.map_top, LinearEquiv.range]

variable {E M : Type} [AddCommGroup E] [Module O E] [AddCommGroup M] [Module O M]

theorem quot_equiv_iff (L₁ L₂ : Lattice (O := O) ρ) (act : G → E → E) (π : Representation O G M)
    (p : E →ₗ[O] M) (hp : Function.Surjective p) (hact : ∀ g x, p (act g x) = π g (p x)) :
    (∃ e : (E ⧸ LinearMap.ker p) ≃ₗ[O] (↥L₁.T ⧸ L₂.T.comap L₁.T.subtype),
      ∀ (g : G) (x : E) (y : ↥L₁.T), e (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
        e (Submodule.Quotient.mk (act g x)) = Submodule.Quotient.mk ⟨ρ g y, L₁.stable g y y.2⟩) ↔
    ∃ q : ↥L₁.T →ₗ[O] M, Function.Surjective q ∧ (∀ g x, q (latRep L₁ g x) = π g (q x)) ∧
      ∀ x, q x = 0 ↔ (x : V) ∈ L₂.T := by
  constructor
  · rintro ⟨e, he⟩
    let Φ := p.quotKerEquivOfSurjective hp
    refine ⟨(Φ.toLinearMap.comp e.symm.toLinearMap).comp (L₂.T.comap L₁.T.subtype).mkQ, ?_, ?_, ?_⟩
    · exact Φ.surjective.comp (e.symm.surjective.comp (Submodule.mkQ_surjective _))
    · intro g y
      obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (e.symm (Submodule.Quotient.mk y))
      have h1 : e (Submodule.Quotient.mk x) = Submodule.Quotient.mk y := by
        rw [hx, LinearEquiv.apply_symm_apply]
      have h3 : latRep L₁ g y = ⟨ρ g y, L₁.stable g y y.2⟩ := Subtype.ext (latRep_apply L₁ g y)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.mkQ_apply]
      rw [h3, ← he g x y h1, LinearEquiv.symm_apply_apply, ← hx]
      simp only [Φ, LinearMap.quotKerEquivOfSurjective_apply_mk]
      exact hact g x
    · intro y
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.mkQ_apply,
        LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
        Submodule.coe_subtype]
  · rintro ⟨q, hq, hqe, hqk⟩
    have hker : LinearMap.ker q = L₂.T.comap L₁.T.subtype := by
      ext y
      simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype, hqk]
    let ψ : M ≃ₗ[O] (↥L₁.T ⧸ L₂.T.comap L₁.T.subtype) :=
      (q.quotKerEquivOfSurjective hq).symm.trans (Submodule.quotEquivOfEq _ _ hker)
    have hψ : ∀ y, ψ (q y) = Submodule.Quotient.mk y := by
      intro y
      simp only [ψ, LinearEquiv.trans_apply]
      rw [(LinearEquiv.symm_apply_eq _).2 (LinearMap.quotKerEquivOfSurjective_apply_mk q hq y).symm]
      rfl
    have hΦ : ∀ x, p.quotKerEquivOfSurjective hp (Submodule.Quotient.mk x) = p x :=
      LinearMap.quotKerEquivOfSurjective_apply_mk p hp
    refine ⟨(p.quotKerEquivOfSurjective hp).trans ψ, fun g x y h => ?_⟩
    simp only [LinearEquiv.trans_apply, hΦ] at h ⊢
    have hxy : p x = q y := ψ.injective (h.trans (hψ y).symm)
    have h3 : latRep L₁ g y = ⟨ρ g y, L₁.stable g y y.2⟩ := Subtype.ext (latRep_apply L₁ g y)
    rw [hact, hxy, ← hqe, h3, hψ]

end Lat

section Sum
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL] {n : ℕ}
    {emb : ZMod n → (K₀ →ₐ[Qp] LL)} {lam : O} {jT : ZMod n → ℤ → ℤ} {cT : G → Polynomial LL}

def ofFull (F : tableLineDegreeTwo.FullRep PD emb lam jT cT) : GRep G Qp LL O where
  V := F.V
  cadd := IsModuleTopology.toContinuousAdd LL F.V
  csmul := by have := IsModuleTopology.toContinuousSMul LL F.V; infer_instance
  ρ := F.ρ
  cont := F.full.1

def sumFull {m : ℕ} (F : Fin m → tableLineDegreeTwo.FullRep PD emb lam jT cT) : GRep G Qp LL O where
  V := ∀ j, (F j).V
  cadd := IsModuleTopology.toContinuousAdd LL _
  csmul := by have := IsModuleTopology.toContinuousSMul LL (∀ j, (F j).V); infer_instance
  ρ := tableLineDegreeTwo.piRep F
  cont := fun x => continuous_pi fun j => (F j).full.1 (x j)

def toFull (A : GRep G Qp LL O) (h : tableLineDegreeTwo.IsFull PD emb lam jT cT A.ρ) : tableLineDegreeTwo.FullRep PD emb lam jT cT where
  V := A.V
  ρ := A.ρ
  full := h

private theorem mapLattice_quotient_of_equivariant_equiv {G LL O V W M : Type} [Group G] [Field LL] [CommRing O] [Algebra O LL]
    [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    [AddCommGroup W] [Module LL W] [Module O W] [IsScalarTower O LL W]
    {ρ : Representation LL G V} {σ : Representation LL G W} [AddCommGroup M] [Module O M]
    (π : Representation O G M) (e : V ≃ₗ[LL] W) (he : ∀ g x, e (ρ g x) = σ g (e x))
    (L₁ L₂ : Lattice (O := O) ρ) (q : ↥L₁.T →ₗ[O] M) (hq : Function.Surjective q)
    (hqe : ∀ g x, q (latRep L₁ g x) = π g (q x)) (hqk : ∀ x, q x = 0 ↔ (x : V) ∈ L₂.T) :
    ∃ q' : ↥(mapLat e he L₁).T →ₗ[O] M, Function.Surjective q' ∧
      (∀ g x, q' (latRep (mapLat e he L₁) g x) = π g (q' x)) ∧
      ∀ x, q' x = 0 ↔ (x : W) ∈ (mapLat e he L₂).T := by
  let s : ↥L₁.T ≃ₗ[O] ↥(mapLat e he L₁).T := (e.restrictScalars O).submoduleMap L₁.T
  have hsx : ∀ x, (s x : W) = e x := fun x => rfl
  refine ⟨q.comp s.symm.toLinearMap, hq.comp s.symm.surjective, ?_, ?_⟩
  · intro g y
    obtain ⟨x, rfl⟩ := s.surjective y
    have hs : latRep (mapLat e he L₁) g (s x) = s (latRep L₁ g x) := by
      apply Subtype.ext
      rw [latRep_apply, hsx, hsx, latRep_apply, he]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hs, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    exact hqe g x
  · intro y
    obtain ⟨x, rfl⟩ := s.surjective y
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, hqk, hsx]
    change (x : V) ∈ L₂.T ↔ e x ∈ L₂.T.map ((e.restrictScalars O : V ≃ₗ[O] W) : V →ₗ[O] W)
    constructor
    · intro h
      exact ⟨x, h, rfl⟩
    · rintro ⟨z, hz, hze⟩
      have hzx : z = (x : V) := e.injective hze
      rwa [← hzx]

omit [IsTopologicalRing LL] in

theorem admissible_quotient_ker_iff_full_lattices {E M : Type} [AddCommGroup E] [Module O E] [AddCommGroup M] [Module O M]
    (act : G → E → E) (π : Representation O G M)
    (p : E →ₗ[O] M) (hp : Function.Surjective p) (hact : ∀ g x, p (act g x) = π g (p x)) :
    tableLineDegreeTwo.AdmQ PD emb lam jT cT act (LinearMap.ker p) ↔
      ∃ (μ : ℕ) (F : Fin μ → GRep G Qp LL O) (A : GRep G Qp LL O)
      (e : A.V ≃ₗ[LL] (∀ j, (F j).V)) (L₁ L₂ : Lattice (O := O) A.ρ) (q : ↥L₁.T →ₗ[O] M),
      (∀ j, tableLineDegreeTwo.IsFull PD emb lam jT cT (F j).ρ) ∧ (∀ g x j, e (A.ρ g x) j = (F j).ρ g (e x j)) ∧ L₂.T ≤ L₁.T ∧
      Function.Surjective q ∧ (∀ g x, q (latRep L₁ g x) = π g (q x)) ∧ ∀ x, q x = 0 ↔ (x : A.V) ∈ L₂.T := by
  constructor
  · rintro ⟨m, F, L₁, L₂, hle, e, he⟩
    obtain ⟨q, hq, hqe, hqk⟩ := (quot_equiv_iff L₁ L₂ act π p hp hact).1 ⟨e, he⟩
    exact ⟨m, fun j => ofFull (F j), sumFull F, LinearEquiv.refl LL _, L₁, L₂, q,
      fun j => (F j).full, fun g x j => rfl, hle, hq, hqe, hqk⟩
  · rintro ⟨μ, F, A, e, L₁, L₂, q, hF, he, hle, hq, hqe, hqk⟩
    let F' : Fin μ → tableLineDegreeTwo.FullRep PD emb lam jT cT := fun j => toFull (F j) (hF j)
    let e' : A.V ≃ₗ[LL] (∀ j, (F' j).V) := e
    have he' : ∀ g x, e' (A.ρ g x) = tableLineDegreeTwo.piRep F' g (e' x) := fun g x => funext fun j => he g x j
    obtain ⟨q', hq', hqe', hqk'⟩ := mapLattice_quotient_of_equivariant_equiv π e' he' L₁ L₂ q hq hqe hqk
    exact ⟨μ, F', mapLat e' he' L₁, mapLat e' he' L₂, Submodule.map_mono hle,
      (quot_equiv_iff _ _ act π p hp hact).2 ⟨q', hq', hqe', hqk'⟩⟩

omit [TopologicalSpace G] [TopologicalSpace LL] [IsTopologicalRing LL] in

theorem resPoly_eq {V : Type} [AddCommGroup V] [Module LL V] [FiniteDimensional LL V]
    (ρ : Representation LL G V) (χ : ℕ → G →* Oˣ) (t : ℕ) :
    tableLineDegreeTwo.resPoly ρ χ t = fun g => LinearMap.charpoly (ρ g) *
      ∏ c : Fin t, (X - C (algebraMap O LL (χ (c.val + 1) g))) := by
  funext g
  simp only [tableLineDegreeTwo.resPoly]
  congr 1
  symm
  refine Finset.prod_bij (fun (c : Fin t) _ => c.val + 1) ?_ ?_ ?_ ?_
  · intro c _
    simp only [Finset.mem_Icc]
    omega
  · intro a _ b _ hab
    exact Fin.ext (by simpa using hab)
  · intro b hb
    simp only [Finset.mem_Icc] at hb
    exact ⟨⟨b - 1, by omega⟩, Finset.mem_univ _, by simp only; omega⟩
  · intro c _
    simp [tableLineDegreeTwo.charL]

end Sum

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P)

theorem isFull_iff_polyFull (jT : ZMod S.n → ℤ → ℤ) (A : GRep S.G ℚ_[l] ↥S.LL.1 S.O) :
    tableLineDegreeTwo.IsFull (P.PD S.K) S.emb S.Γ.lam jT (tableLineDegreeTwo.resPoly S.Γ.T₀.ρ S.Γ.chi S.D.t) A.ρ ↔ PolyFull S jT A := by
  unfold tableLineDegreeTwo.IsFull PolyFull
  rw [resPoly_eq]
  simp only [tableLineDegreeTwo.Over, AlgHom.ext_iff, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
  exact ⟨fun h => ⟨h.2.1, h.2.2.1, h.2.2.2⟩, fun h => ⟨A.cont, h.1, h.2.1, h.2.2⟩⟩

theorem admissibleQuotient_iff_admissible_module : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) (jT : ZMod S.n → ℤ → ℤ), (∀ i a, ((S.D.Ut i).count a : ℤ) = jT i a) → ∀ (E M : Type) [AddCommGroup E] [Module S.O E] [AddCommGroup M] [Module S.O M] (act : S.G → E → E) (π : Representation S.O S.G M) (p : E →ₗ[S.O] M), Function.Surjective p → (∀ g x, p (act g x) = π g (p x)) → (tableLineDegreeTwo.AdmQ (P.PD S.K) S.emb S.Γ.lam jT (tableLineDegreeTwo.resPoly S.Γ.T₀.ρ S.Γ.chi S.D.t) act (LinearMap.ker p) ↔ S.admitted π) := by
  intro l _ P S jT hj E M _ _ _ _ act π p hp hact
  refine (admissible_quotient_ker_iff_full_lattices act π p hp hact).trans (Iff.trans ?_ (admissibleModule_iff_lattice_quotients S hj π).symm)
  constructor
  · rintro ⟨μ, F, A, e, L₁, L₂, q, hF, h⟩
    exact ⟨μ, F, A, e, L₁, L₂, q, fun j => (isFull_iff_polyFull S jT (F j)).1 (hF j), h⟩
  · rintro ⟨μ, F, A, e, L₁, L₂, q, hF, h⟩
    exact ⟨μ, F, A, e, L₁, L₂, q, fun j => (isFull_iff_polyFull S jT (F j)).2 (hF j), h⟩

end GlobalTheory.FullCharpoly
