import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyOfModToModIso

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieMet GlobalTheory.LocM GlobalTheory.Points
open GlobalTheory.GradedPieces IsLocalRing

namespace GlobalTheory.LocM.FJ

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Value

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

structure GrTriv (Z : Mdl Y i₀) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) (F : Z.X.Modules) : Type 1 where

  L : LB Z.X

  isLB : L.IsLB

  hU : ∀ i, IsAffineOpen (L.U i)

  w : ∀ i, Vecs Dw (Y Z.i).t Γ(Z.X, L.U i)

  int : ∀ i, IntFrame Z (hU i) (w i)

  trans : ∀ (i i' : L.ι) (k : Type) [Field k] (φ : Γ(Z.X, L.U i) →+* k) (φ' : Γ(Z.X, L.U i') →+* k)
    (d : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → k),
    spMap φ ≫ (hU i).fromSpec = spMap φ' ≫ (hU i').fromSpec → Set.range (spMap φ ≫ (hU i).fromSpec) ⊆ Z.opn →
    (∀ σ, DiagAt (Y Z.i).t (spMap φ ≫ (hU i).fromSpec ≫ Z.π) ((w i').bc φ' σ) ((w i).bc φ σ) (d σ)) →
    valR (spMap φ ≫ (hU i).fromSpec) _ (L.g i i').val = ∏ σ, ∏ a, d σ a ^ e σ a

  iso : F ≅ GlobalTheory.LB.toMod L

variable {Z : Mdl Y i₀} {e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ}

theorem nonempty_grTriv (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) {L : LB Z.X} (h : IsGrLB Z e L) :
    Nonempty (GrTriv Z e (Z.ofMod (GlobalTheory.LB.toMod L)).toMod) := by
  obtain ⟨hL, hU, w, hw, ht⟩ := h
  haveI : GlobalTheory.QCoh.IsFiniteQC (GlobalTheory.LB.toMod L) := (GlobalTheory.VB.isVB_toMod hL).isFiniteQC
  obtain ⟨i⟩ := GlobalTheory.ModelPresentation.nonempty_ofMod_toMod_iso E H Dw Xo p W hp hW Y i₀ Z (GlobalTheory.LB.toMod L)
  exact ⟨⟨L, hL, hU, w, hw, ht, i⟩⟩

variable {F : Z.X.Modules} (T : GrTriv Z e F) {V : Z.X.Opens} {k : Type} [Field k]

def GrTriv.IsVal (f : Γ(F, V)) (x : Sp k ⟶ Z.X) (u : Vecs Dw (Y Z.i).t k) (r : k) : Prop :=
  ⊤ ≤ x ⁻¹ᵁ V ∧ ∃ (i : T.L.ι) (φ : Γ(Z.X, T.L.U i) →+* k) (d : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → k),
    spMap φ ≫ (T.hU i).fromSpec = x ∧ (∀ σ, DiagAt (Y Z.i).t (x ≫ Z.π) ((T.w i).bc φ σ) (u σ) (d σ)) ∧
    r = valR x (V ⊓ T.L.U i) (GlobalTheory.LB.coord (T.iso.hom.app V f) i) * ∏ σ, ∏ a, d σ a ^ e σ a

theorem range_subset_opn {x : Sp k ⟶ Z.X} {u : Vecs Dw (Y Z.i).t k} (h : Z.FlagAt x u) : Set.range x ⊆ Z.opn := by
  obtain ⟨a, φ, rfl, -⟩ := h
  rintro _ ⟨z, rfl⟩
  rw [← Z.cover]
  exact Set.mem_iUnion.2 ⟨a, le_preimage_specMap_fromSpec (Z.U a).2 (CommRingCat.ofHom φ) (Set.mem_univ z)⟩

theorem GrTriv.existsUnique_isVal (hty : ∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) (f : Γ(F, V)) {x : Sp k ⟶ Z.X}
    (hx : ⊤ ≤ x ⁻¹ᵁ V) {u : Vecs Dw (Y Z.i).t k} (hu : Z.FlagAt x u) : ∃! r, T.IsVal f x u r := by
  have ho := range_subset_opn hu
  have tu : ∀ σ i, IsTanAtG (Y Z.i).t (x ≫ Z.π) (u σ i) := fun σ i => by
    obtain ⟨_, _, -, h, -⟩ := hu
    exact (h.1 σ i).1
  have fl : ∀ i (φ : Γ(Z.X, T.L.U i) →+* k), spMap φ ≫ (T.hU i).fromSpec = x → Z.FlagAt x ((T.w i).bc φ) :=
    fun i φ h => h ▸ (T.int i).2 k φ (h ▸ ho)
  refine existsUnique_of_exists_of_unique ?_ ?_
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (T.isLB.cover.ge (Set.mem_univ (x (closedPoint k))))
    have h : ⊤ ≤ x ⁻¹ᵁ T.L.U i := fun z _ => by
      obtain rfl : z = closedPoint k := Subsingleton.elim (α := PrimeSpectrum k) _ _
      exact hi
    have e₁ := specMap_valMap_fromSpec (T.hU i) x h
    choose d hd using fun σ => exists_diag_of_flagAt Z hty hu (fl i _ e₁) σ (tu σ) (tan_bc (T.int i) _ e₁ σ)
      (linInd_bc (T.int i) _ e₁ σ)
    exact ⟨_, hx, i, _, d, e₁, fun σ => (diagAt_iff (tan_bc (T.int i) _ e₁ σ) (tu σ) (d σ)).2 (hd σ), rfl⟩
  · rintro _ _ ⟨-, i, φ, d, e₁, hd, rfl⟩ ⟨-, i', φ', d', e₂, hd', rfl⟩
    choose D hD using fun σ => exists_diag_of_flagAt Z hty (fl i _ e₁) (fl i' _ e₂) σ (tan_bc (T.int i) _ e₁ σ)
      (tan_bc (T.int i') _ e₂ σ) (linInd_bc (T.int i') _ e₂ σ)
    have hg := T.trans i i' k φ φ' D (e₁.trans e₂.symm) (e₁ ▸ ho) fun σ => by
      rw [← Category.assoc, e₁]
      exact (diagAt_iff (tan_bc (T.int i') _ e₂ σ) (tan_bc (T.int i) _ e₁ σ) (D σ)).2 (hD σ)
    have hd'' : ∀ σ, d' σ = fun a => d σ a * D σ a := fun σ =>
      ((diagAt_iff (tan_bc (T.int i') _ e₂ σ) (tu σ) _).1 (hd' σ)).unique (linInd_bc (T.int i') _ e₂ σ)
        ((hD σ).trans ((diagAt_iff (tan_bc (T.int i) _ e₁ σ) (tu σ) _).1 (hd σ)))
    have h₁ : ⊤ ≤ x ⁻¹ᵁ T.L.U i := e₁ ▸ le_preimage_specMap_fromSpec (T.hU i) (CommRingCat.ofHom φ)
    have h₂ : ⊤ ≤ x ⁻¹ᵁ T.L.U i' := e₂ ▸ le_preimage_specMap_fromSpec (T.hU i') (CommRingCat.ofHom φ')
    have h₃ : ⊤ ≤ x ⁻¹ᵁ (V ⊓ T.L.U i ⊓ T.L.U i') := fun z hz => ⟨⟨hx hz, h₁ hz⟩, h₂ hz⟩
    have hc := congrArg (valR x _) (GlobalTheory.LB.coord_mem (T.iso.hom.app V f) i i')
    rw [valR_mul x _ h₃] at hc
    erw [valR_res x _ h₃, valR_res x _ h₃, valR_res x _ h₃] at hc
    rw [e₁] at hg
    rw [hc, hg]
    simp only [hd'', mul_zpow, Finset.prod_mul_distrib]
    ring

theorem GrTriv.IsVal.change {T : GrTriv Z e F} {f : Γ(F, V)} {x : Sp k ⟶ Z.X} {u u' : Vecs Dw (Y Z.i).t k} {r : k}
    (h : T.IsVal f x u r) (tu : ∀ σ i, IsTanAtG (Y Z.i).t (x ≫ Z.π) (u σ i))
    (tu' : ∀ σ i, IsTanAtG (Y Z.i).t (x ≫ Z.π) (u' σ i)) {d : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → k}
    (hd : ∀ σ, DiagAt (Y Z.i).t (x ≫ Z.π) (u σ) (u' σ) (d σ)) : T.IsVal f x u' (r * ∏ σ, ∏ a, d σ a ^ e σ a) := by
  obtain ⟨hx, i, φ, D, e₁, hD, rfl⟩ := h
  refine ⟨hx, i, φ, fun σ a => d σ a * D σ a, e₁, fun σ => (diagAt_iff (tan_bc (T.int i) _ e₁ σ) (tu' σ) _).2
    (((diagAt_iff (tan_bc (T.int i) _ e₁ σ) (tu σ) _).1 (hD σ)).trans ((diagAt_iff (tu σ) (tu' σ) _).1 (hd σ))), ?_⟩
  simp only [mul_zpow, Finset.prod_mul_distrib]
  ring

theorem GrTriv.isVal_chart (f : Γ(F, V)) {x : Sp k ⟶ Z.X} (hx : ⊤ ≤ x ⁻¹ᵁ V) (i : T.L.ι) (φ : Γ(Z.X, T.L.U i) →+* k)
    (h : spMap φ ≫ (T.hU i).fromSpec = x) :
    T.IsVal f x ((T.w i).bc φ) (valR x (V ⊓ T.L.U i) (GlobalTheory.LB.coord (T.iso.hom.app V f) i)) :=
  ⟨hx, i, φ, fun _ _ => 1, h, fun σ => (diagAt_iff (tan_bc (T.int i) _ h σ) (tan_bc (T.int i) _ h σ) _).2 (Diag.refl _),
    by simp⟩

end Value

end GlobalTheory.LocM.FJ
