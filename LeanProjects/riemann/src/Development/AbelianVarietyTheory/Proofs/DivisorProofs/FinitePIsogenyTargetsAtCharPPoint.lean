import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogTarget
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpSchemeSquareProductMapEqTensorHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteKernelsPIsogeniesHarrisTaylorCharPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPIsogPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsObjMapCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyOfFinitePresentationOfIsQProjOver

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UPel.HT.ES.CorrQF

theorem charP_of_residueField_of_notMem_basicOpen (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (u : X)
    (hu : u ∉ X.basicOpen ((p : ℕ) : Γ(X, ⊤))) (L : Type) [Field L] (h : X.residueField u →+* L) : CharP L p := by
  have h1 : ¬ IsUnit (X.presheaf.germ ⊤ u trivial ((p : ℕ) : Γ(X, ⊤))) :=
    fun hh => hu ((X.mem_basicOpen ((p : ℕ) : Γ(X, ⊤)) u (Set.mem_univ u)).2 hh)
  rw [map_natCast] at h1
  have h2 : IsLocalRing.residue (X.presheaf.stalk u) ((p : ℕ) : X.presheaf.stalk u) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 h1)
  rw [map_natCast] at h2
  have h3 : ((p : ℕ) : L) = 0 := by
    rw [← map_natCast h]
    exact (congrArg h h2).trans (map_zero h)
  exact (CharP.charP_iff_prime_eq_zero (Fact.out)).2 h3

theorem finite_isogTarget : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 → ∀ (c : ℕ) (M : Model b N) (u : M.X), u ∉ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) → ∀ (L : Type) [Field L] [IsAlgClosed L] (h : M.X.residueField u →+* L), {ζ : Sp L ⟶ M.X | CorrQF.IsogTarget M c (spMap h ≫ M.X.fromSpecResidueField u) ζ}.Finite := by
  intro p _ D R _ b N hN hNp hm c M u hu L _ _ h
  haveI : CharP L p := charP_of_residueField_of_notMem_basicOpen p M.X u hu L h
  set ξ := spMap h ≫ M.X.fromSpecResidueField u with hξ
  obtain ⟨o₀, ⟨m₀⟩⟩ := HTPull.exists_objMap_pull p D R b N M.X (Sp L) M.s ξ M.univ
  have hF := T.finite_kernels_pIsogenies_harrisTaylor_charP p D R b N hN hNp hm c L (ξ ≫ M.s) o₀
  let Rel : (Sp L ⟶ M.X) → ((T : Over (Sp L)) → (T ⟶ o₀.A) → Prop) → Prop := fun ζ P =>
    ∃ (o' : Obj b N (ξ ≫ M.s)) (ψ₀ : o₀.A ⟶ o'.A), IsPIsog c o₀ o' ψ₀ ∧
      (P = fun T x => x ≫ ψ₀ = 1) ∧ Nonempty (ObjMap o' M.univ ζ) ∧ ζ ≫ M.s = ξ ≫ M.s
  have hsub : ∀ P, {ζ | Rel ζ P}.Subsingleton := by
    rintro P ζ₁ ⟨o₁, ψ₁, hψ₁, rfl, ⟨n₁⟩, hs₁⟩ ζ₂ ⟨o₂, ψ₂, hψ₂, he, ⟨n₂⟩, hs₂⟩
    obtain ⟨m, -⟩ := KerDet.exists_objMap_of_ker_eq p D R b N hN hNp c (Sp L) (ξ ≫ M.s) o₀ o₁ o₂ ψ₁ ψ₂
      hψ₁ hψ₂ (fun T x => Iff.of_eq (congrFun (congrFun he T) x))
    have e := (M.rep (Sp L) (ξ ≫ M.s) o₁).unique ⟨hs₁, ⟨n₁⟩⟩
      ⟨by rw [Category.assoc, hs₂, Category.id_comp], ⟨m.comp n₂⟩⟩
    rw [Category.id_comp] at e
    exact e
  refine (hF.biUnion fun P _ => (hsub P).finite).subset ?_
  intro ζ hζ
  obtain ⟨hs, o, o', ψ, ⟨mo⟩, ⟨mo'⟩, hψ⟩ := hζ
  obtain ⟨i₀, -⟩ := IwLevel.exists_objMap_cancel (f := 𝟙 (Sp L)) (g := ξ)
    (cast (congrArg (ObjMap o₀ M.univ) (Category.id_comp ξ).symm) m₀) mo
  obtain ⟨i₁, -⟩ := IwLevel.exists_objMap_cancel (f := 𝟙 (Sp L)) (g := ζ)
    (cast (congrArg (ObjMap o' M.univ) (Category.id_comp ζ).symm) mo') mo'
  obtain ⟨ψ₀, hψ₀, -⟩ := ValExt.isPIsog_pull p D R b N c (Sp L) (Sp L) (ξ ≫ M.s) (ξ ≫ M.s) (𝟙 _)
    o o' o₀ o' i₀ i₁ ψ hψ
  exact Set.mem_biUnion (x := fun T x => x ≫ ψ₀ = 1) ⟨o', ψ₀, hψ₀, rfl⟩ ⟨o', ψ₀, hψ₀, rfl, ⟨mo'⟩, hs.symm⟩

end GlobalTheory.UPel.HT.ES.CorrQF
