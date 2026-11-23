import Development.EtaleCohomology.EtaleSheaves.CokernelKilling
import Development.EtaleCohomology.EtaleSheaves.CokernelKilling.FiniteSubcover

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.KillCokPf.Asm

abbrev piMap {D : CommRingCat.{0}} {ι : Type} (D₁ : ι → CommRingCat.{0}) (e : ∀ k, D ⟶ D₁ k) :
    D ⟶ CommRingCat.of (∀ k, D₁ k) :=
  CommRingCat.ofHom (Pi.ringHom fun k => (e k).hom)

def ProdGlue : Prop := Coprod → ∀ (q : ℕ) [NeZero q] (i : ℤ) {D Y' : CommRingCat.{0}} (φ' : D ⟶ Y') (m : ℤ)
  (y : H (ZMod q) (sch.obj (Spec Y')) (tw q i) m) {ι : Type} [Fintype ι] (D₁ : ι → CommRingCat.{0}) (e : ∀ k, D ⟶ D₁ k),
  (∀ k, Et (e k)) →
  (∀ k, ∃ (Y₁ : CommRingCat.{0}) (u : Y' ⟶ Y₁) (φ₁ : D₁ k ⟶ Y₁), IsPushout φ' (e k) u φ₁ ∧
      pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ₁)) (tw q i) m)) →
  Et (piMap D₁ e) ∧ ∃ (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : CommRingCat.of (∀ k, D₁ k) ⟶ Y''),
    IsPushout φ' (piMap D₁ e) u φ'' ∧
    pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ'')) (tw q i) m)

theorem sps_pi {D : CommRingCat.{0}} {ι : Type} (D₁ : ι → CommRingCat.{0}) (e : ∀ k, D ⟶ D₁ k)
    (hc : ∀ x : PrimeSpectrum D, ∃ k, x ∈ Set.range (PrimeSpectrum.comap (e k).hom)) : SpS (piMap D₁ e) := by
  intro r hr
  obtain ⟨k, P, hP⟩ := hc ⟨r, hr⟩
  refine ⟨P.asIdeal.comap (Pi.evalRingHom (fun k => D₁ k) k), Ideal.comap_isPrime _ _, ?_⟩
  have h := congrArg PrimeSpectrum.asIdeal hP
  simp only [PrimeSpectrum.comap_asIdeal] at h
  rw [← h, Ideal.comap_comap]
  rfl

theorem Assemble_of (hG : ProdGlue) : LateralTheory.E.KillCokPf.Assemble := by
  intro hC q _ i D Y' φ' m y hloc
  have h' : ∀ x : PrimeSpectrum D, ∃ (D₁ : CommRingCat.{0}) (e : D ⟶ D₁), Et e ∧
      x ∈ Set.range (PrimeSpectrum.comap e.hom) ∧
      ∃ (Y₁ : CommRingCat.{0}) (u : Y' ⟶ Y₁) (φ₁ : D₁ ⟶ Y₁), IsPushout φ' e u φ₁ ∧
      pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ₁)) (tw q i) m) := by
    intro x
    obtain ⟨D₁, e, Q₁, he, hQ₁, hc, rest⟩ := hloc x.asIdeal x.isPrime
    exact ⟨D₁, e, he, ⟨⟨Q₁, hQ₁⟩, PrimeSpectrum.ext hc⟩, rest⟩
  choose D₁ e he hx hY using h'
  obtain ⟨s, hs⟩ := LateralTheory.E.KillCokPf.Lem.finite_subcover D₁ e he hx
  obtain ⟨het, Y'', u, φ'', hpo, hy⟩ := hG hC q i φ' m y (ι := s) (fun k => D₁ k.1) (fun k => e k.1)
    (fun k => he k.1) (fun k => hY k.1)
  refine ⟨_, _, Y'', u, φ'', het, sps_pi _ _ ?_, hpo, hy⟩
  intro x
  obtain ⟨r, hr, hxr⟩ := hs x
  exact ⟨⟨r, hr⟩, hxr⟩

end LateralTheory.E.KillCokPf.Asm
