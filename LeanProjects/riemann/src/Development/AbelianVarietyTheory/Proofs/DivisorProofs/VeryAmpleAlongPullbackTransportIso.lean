import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfIsDominant
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem gs_abCst {R : Type} [CommRing R] {X Z : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (W : X.Opens)
    (r : Z ⟶ X) (z : Z) (hz : r z ∈ W) (x : R) :
    gs r z W (GlobalTheory.AbLaw.cst f W x) = gs (r ≫ f) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) :=
  (gs_res r z le_top hz _).trans (gs_pull r f z ⊤ trivial _)

theorem gs_top_mul {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (a b : R) :
    gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (a * b)) =
      gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) *
        gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom b) := by
  rw [map_mul]; exact gs_mul q z ⊤ trivial _ _

theorem isUnit_gs_top {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (a : Rˣ) :
    IsUnit (gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (a : R))) := by
  rw [gs_eq q z ⊤ trivial]
  exact ((a.isUnit.map _).map _).map _

theorem veryAmpleAlong_transport {K : Type} [Field K] {X Y XA : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of K))
    (pA : XA ⟶ Spec (CommRingCat.of K)) (gn : Y ⟶ XA) [IsIso gn] (hp : gn ≫ pA = p) (π : Y ⟶ X) {L : LB X}
    (hL : L.IsLB) {LA : LB XA} (hLA : LA.IsLB) {k m : ℕ} (b : Fin (m + 1) → H0 LA k)
    (hb : VeryAmpleAlong pA (𝟙 XA) LA b) (σ : Fin (m + 1) → H0 L k) (c : Fin (m + 1) → Kˣ)
    (H : ∀ (y : Y) (j : Fin 1 → L.ι) (jA : Fin 1 → LA.ι), π y ∈ L.U (j 0) → gn y ∈ LA.U (jA 0) →
      ∃ u : (Y.presheaf.stalk y)ˣ, ∀ i, secGerm π y (σ i) j =
        u.val * gs p y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c i : K)) * secGerm gn y (b i) jA) :
    VeryAmpleAlong p π L σ := by
  classical

  have hmem : ∀ i (y : Y), y ∈ π ⁻¹ᵁ nonzeroLocus (σ i) ↔ gn y ∈ (𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i) := by
    intro i y
    obtain ⟨j, hj⟩ := exists_chart hL (π y)
    obtain ⟨jA, hjA⟩ := exists_chart hLA (gn y)
    obtain ⟨u, hu⟩ := H y (fun _ => j) (fun _ => jA) hj hjA
    change π y ∈ nonzeroLocus (σ i) ↔ gn y ∈ nonzeroLocus (b i)
    rw [GlobalTheory.SectionRingIso.mem_iff_isUnit (σ i) π y (j := fun _ => j) hj,
      GlobalTheory.SectionRingIso.mem_iff_isUnit (b i) gn y (j := fun _ => jA) hjA]
    change IsUnit (secGerm π y (σ i) _) ↔ IsUnit (secGerm gn y (b i) _)
    rw [hu i, _root_.mul_assoc, IsUnit.mul_iff, IsUnit.mul_iff]
    simp only [u.isUnit, isUnit_gs_top p y (c i), true_and]
  have hW : ∀ i, π ⁻¹ᵁ nonzeroLocus (σ i) = gn ⁻¹ᵁ ((𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i)) := fun i =>
    TopologicalSpace.Opens.ext (Set.ext fun y => hmem i y)
  refine ⟨?_, fun i => ⟨?_, ?_⟩⟩
  ·
    refine eq_top_iff.2 fun y _ => ?_
    have : gn y ∈ ⨆ i, (𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i) := hb.1 ▸ trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (hmem i y).2 hi⟩
  · rw [hW i]; exact (hb.2 i).1.preimage gn
  · obtain ⟨-, ρ, hρ, hs⟩ := hb.2 i
    have le : π ⁻¹ᵁ nonzeroLocus (σ i) ≤ gn ⁻¹ᵁ ((𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i)) := (hW i).le
    have ge : gn ⁻¹ᵁ ((𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i)) ≤ π ⁻¹ᵁ nonzeroLocus (σ i) := (hW i).ge
    let φ : Γ(XA, (𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i)) →+* Γ(Y, π ⁻¹ᵁ nonzeroLocus (σ i)) :=
      (GlobalTheory.AbLaw.rs Y le).comp (gn.app _).hom
    have gsφ : ∀ y (hy : y ∈ π ⁻¹ᵁ nonzeroLocus (σ i)) (a : Γ(XA, (𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i))),
        gs (𝟙 Y) y _ (φ a) = gs gn y _ a := fun y hy a =>
      (gs_res (𝟙 Y) y le hy _).trans ((gs_pull (𝟙 Y) gn y _ (le hy) a).trans (by rw [Category.id_comp]))
    have hφc : ∀ x : K, φ (GlobalTheory.AbLaw.cst pA _ x) = GlobalTheory.AbLaw.cst p (π ⁻¹ᵁ nonzeroLocus (σ i)) x := fun x =>
      fn_ext fun y hy => by
        rw [gsφ y hy, gs_abCst pA _ gn y (le hy), gs_abCst p _ (𝟙 Y) y hy, hp, Category.id_comp]
    let r : Fin (m + 1) → Γ(Y, π ⁻¹ᵁ nonzeroLocus (σ i)) := fun j =>
      GlobalTheory.AbLaw.cst p (π ⁻¹ᵁ nonzeroLocus (σ i)) ((c j : K) / c i) * φ (ρ j)
    refine ⟨r, ?_, ?_⟩
    · intro j ch a ha hch
      obtain ⟨jA, hjA⟩ := exists_chart hLA (gn a)
      obtain ⟨u, hu⟩ := H a ch (fun _ => jA) (GlobalTheory.SectionRingIso.mem_ch.1 hch) hjA
      have haW : a ∈ π ⁻¹ᵁ nonzeroLocus (σ i) := ha
      have haV : gn a ∈ (𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i) := le haW
      have hA : (𝟙 XA) (gn a) ∈ secChart LA (fun _ => jA) := GlobalTheory.SectionRingIso.mem_ch.2 hjA
      have key : ∀ j', secGerm gn a (b j') (fun _ => jA) =
          (gn.stalkMap a).hom (secGerm (𝟙 XA) (gn a) (b j') (fun _ => jA)) := fun j' => by
        have := secGerm_comp gn (𝟙 XA) a (b j') hA
        rwa [Category.comp_id] at this
      have e := congrArg (gn.stalkMap a).hom (hρ j (fun _ => jA) (gn a) haV hA)
      rw [map_mul, ← key, ← key, ← gs_stalkMap gn a _ haV] at e
      have hci : ((c j : K) / c i) * c i = c j := div_mul_cancel₀ _ (c i).ne_zero
      have hcst : gs p a ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c j : K)) =
          gs p a ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom ((c j : K) / c i)) *
            gs p a ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c i : K)) := by
        rw [← gs_top_mul, hci]
      rw [hu j, hu i, gs_mul (𝟙 Y) a _ haW, gs_abCst p _ (𝟙 Y) a haW, gsφ a haW, e, Category.id_comp, hcst]
      ring
    · intro f
      obtain ⟨g0, hg0⟩ := (ConcreteCategory.bijective_of_isIso (gn.app ((𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i)))).2
        (GlobalTheory.AbLaw.rs Y ge f)
      have hf : φ g0 = f := by
        change GlobalTheory.AbLaw.rs Y le ((gn.app _).hom g0) = f
        rw [hg0, GlobalTheory.AbLaw.rs_rs, GlobalTheory.AbLaw.rs_self]
      obtain ⟨P, hP⟩ := hs g0
      have hcomp : φ.comp (MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst pA _) ρ) =
          MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst p (π ⁻¹ᵁ nonzeroLocus (σ i))) (fun j => φ (ρ j)) :=
        MvPolynomial.ringHom_ext (fun x => by rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, hφc])
          (fun j => by rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X'])
      have hρr : ∀ j, MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst p (π ⁻¹ᵁ nonzeroLocus (σ i))) r
          (MvPolynomial.C ((c i : K) / c j) * MvPolynomial.X j) = φ (ρ j) := fun j => by
        have h1 : ((c i : K) / c j) * ((c j : K) / c i) = 1 := by
          rw [div_mul_div_comm, _root_.mul_comm (c i : K)]
          exact div_self (mul_ne_zero (c j).ne_zero (c i).ne_zero)
        rw [map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
        change GlobalTheory.AbLaw.cst p _ ((c i : K) / c j) * (GlobalTheory.AbLaw.cst p _ ((c j : K) / c i) * φ (ρ j)) = φ (ρ j)
        rw [← _root_.mul_assoc, ← map_mul, h1, map_one, _root_.one_mul]
      refine ⟨MvPolynomial.bind₁ (fun j => MvPolynomial.C ((c i : K) / c j) * MvPolynomial.X j) P, ?_⟩
      rw [MvPolynomial.eval₂Hom_bind₁]
      simp only [hρr]
      rw [← hf, ← hP, ← hcomp]
      rfl

end GlobalTheory.Mum
