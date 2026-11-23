import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.Trinv
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GensKill
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.RepQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.ToTMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.PairMf
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.PhiFg
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.StarBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TrinvBaseChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ChEltOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.BcChiTmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DTrCoeff
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinE

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem lift_ex {B C E M : Type} [CommRing B] [CommRing C] [Algebra B C] [Ring E] [Algebra B E] [Ring M]
    [Algebra C M] (ρ : E →+* M) (hρ : ∀ b, ρ (algebraMap B E b) = algebraMap C M (algebraMap B C b)) :
    ∃ r : C ⊗[B] E →ₐ[C] M, ∀ y, r (1 ⊗ₜ y) = ρ y := by
  letI : Algebra B M := Algebra.compHom M (algebraMap B C)
  haveI : IsScalarTower B C M := .of_algebraMap_eq' rfl
  let ρ' : E →ₐ[B] M := { ρ with commutes' := hρ }
  refine ⟨Algebra.TensorProduct.lift (Algebra.ofId C M) ρ' fun s _ => Algebra.commute_algebraMap_left s _, fun y => ?_⟩
  refine (Algebra.TensorProduct.lift_tmul _ _ _ _ _).trans ?_
  rw [map_one, one_mul]
  rfl

private theorem tr_bc {n : ℕ} {B E : Type} [CommRing B] [Ring E] [Algebra B E] (D : Det n B E) (hn : 1 ≤ n)
    (C : Type) [CommRing C] [Algebra B C] (t : C ⊗[B] E →ₗ[C] C) (ht : ∀ y, t (1 ⊗ₜ y) = algebraMap B C (D.tr y))
    (y : C ⊗[B] E) : t y = (D.baseChange C).tr y := by
  obtain ⟨t', ht'⟩ := (d_tr (D.baseChange C)).1 hn
  rw [← ht']
  induction y with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul c z =>
    have : c ⊗ₜ[B] z = c • ((1 : C) ⊗ₜ[B] z) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul, map_smul, ht, ht']
    congr 1
    exact (((d_bc D C).2.2.2 z).2 1).symm

theorem UpperTheory.V.Pa.hat_ex :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∀ {Bh : Type} [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [Algebra Bh (FractionRing x.A)], (∀ b, algebraMap Bh (FractionRing x.A) (algebraMap B Bh b) = algebraMap x.A (FractionRing x.A) (P.f b)) → Nonempty (Hat h x u.D P.ker Bh (G.frame.eps O B)) := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P Bh _ _ _ _ hB
  have hrep : ∀ (g : G.G₀) (b : B), P.rep (MonoidAlgebra.single g b) = P.f b • mat x.ρ (h.p₀ g) := by
    clear hB
    intro g b
    simp only [OoPt.rep, GDet.repAlg, RingHom.comp_apply, MonoidAlgebra.mapRingHom_single,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MonoidAlgebra.lift_single, MonoidHom.coe_comp,
      Function.comp_apply, RingHom.mapMatrix_apply, Algebra.algebraMap_self]
    rfl
  have hρv : ∀ (b : B) (i j : Fin n), (algebraMap x.A (FractionRing x.A)) ((P.rep (MonoidAlgebra.single 1 b)) i j) =
      algebraMap Bh (Matrix (Fin n) (Fin n) (FractionRing x.A)) (algebraMap B Bh b) i j := by
    intro b i j
    rw [hrep, map_one, map_one, Matrix.smul_apply, Matrix.algebraMap_matrix_apply]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq, if_pos rfl, hB, smul_eq_mul, mul_one]
    · rw [Matrix.one_apply_ne hij, if_neg hij, smul_zero, map_zero]
  have hφ : PhiCond G.frame.G₀ l := phi_fg _ P.fg
  have hn : 1 ≤ n := le_trans x.a_pos x.a_le
  haveI : IsAdicComplete (maximalIdeal B) B := IsCO.complete (O := O)
  haveI : CompactSpace G.frame.G₀ :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ G.frame.η_open).isCompact
  obtain ⟨DE, T, hCH, hpull, hst, htr⟩ := trinv u hφ hn P.gens (gens_kill P)
  obtain ⟨hres, -, hh, χ, hred, hmf⟩ := pair_mf u hφ
  obtain ⟨-, hfinB, hcont⟩ := finE u.D χ u.cont hred hmf P.gens
  have hπs : Function.Surjective (u.D.toQuot P.gens) := fun q =>
    Quotient.inductionOn' q fun z => ⟨z, rfl⟩
  obtain ⟨ι, hιs, hιmap, hιker, hιpull⟩ := tens u.D DE (u.D.toQuot P.gens) Bh hπs hpull
  have hker : {z | u.D.toQuot P.gens z = 0} = P.ker := by
    ext z
    change ((z : (u.D.chBar P.gens).ringCon.Quotient) = ((0 : MonoidAlgebra B G.G₀) : _)) ↔ _
    rw [RingCon.eq, TwoSidedIdeal.rel_iff, sub_zero]
    rfl
  rw [hker] at hιker
  have hs : ∀ g : G.G₀, ι (MonoidAlgebra.single g 1) = 1 ⊗ₜ[B] u.D.toQuot P.gens (MonoidAlgebra.single g 1) := by
    intro g
    have := hιmap (MonoidAlgebra.single g 1)
    rwa [MonoidAlgebra.mapRingHom_single, map_one] at this
  haveI : Module.Finite B (u.D.CHQuot P.gens) := hfinB
  obtain ⟨T', hT'st, hT'tr⟩ := trinv_baseChange T Bh
  obtain ⟨ρ0, hρ0⟩ := rep_quot P
  have hρ : ∀ b : B, ((algebraMap x.A (FractionRing x.A)).mapMatrix.comp ρ0)
      (algebraMap B (u.D.CHQuot P.gens) b) =
      algebraMap Bh (Matrix (Fin n) (Fin n) (FractionRing x.A)) (algebraMap B Bh b) := by
    intro b
    have e1 : algebraMap B (u.D.CHQuot P.gens) b = u.D.toQuot P.gens (MonoidAlgebra.single 1 b) :=
      ((u.D.toQuot P.gens).commutes b).symm
    ext i j
    rw [RingHom.comp_apply, e1, hρ0, RingHom.mapMatrix_apply, Matrix.map_apply, hρv]
  obtain ⟨rr, hrr⟩ := lift_ex ((algebraMap x.A (FractionRing x.A)).mapMatrix.comp ρ0) hρ
  have hπg : ∀ (g : G.G₀) (c : B), u.D.toQuot P.gens (MonoidAlgebra.single g c) =
      c • u.D.toQuot P.gens (MonoidAlgebra.single g 1) := by
    intro g c
    rw [← map_smul, MonoidAlgebra.smul_single', mul_one]
  refine ⟨Hat.mk (Bh ⊗[B] u.D.CHQuot P.gens) inferInstance ι hιs hιker (DE.baseChange Bh)
    ((d_chS DE Bh).2.2 hCH).1 hιpull T' (fun y => tr_bc DE hn Bh T'.tr (fun z => by rw [hT'tr, htr]) y)
    (fun g => ?_) rr (fun g => ?_) (Submodule.map (TensorProduct.mk B Bh (u.D.CHQuot P.gens) 1) ⊤)
    (Module.Finite.fg_top.map _) (fun g => ⟨_, trivial, (hs g).symm⟩) (fun j => ?_)⟩
  · rw [hs, hs, hT'st, hst, (star_basic G.frame n O B).2.2.2.2.2.2 g 1, one_mul, hπg,
      TensorProduct.tmul_smul, algebraMap_smul]
  · rw [hs, hrr, RingHom.comp_apply, hρ0, hrep, map_one, one_smul, RingHom.mapMatrix_apply]
  · obtain ⟨U, hU⟩ := hcont j
    refine ⟨U, fun g v hv => ?_⟩
    have hl : u.D.toQuot P.gens (MonoidAlgebra.single g 1) * (u.D.toQuot P.gens (MonoidAlgebra.single v 1) - 1) ∈
        (maximalIdeal B ^ j • ⊤ : Submodule B (u.D.CHQuot P.gens)) := by
      have := Submodule.mem_map_of_mem
        (f := LinearMap.mulLeft B (u.D.toQuot P.gens (MonoidAlgebra.single g 1))) (hU v hv)
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    have key := Submodule.mem_map_of_mem (f := TensorProduct.mk B Bh (u.D.CHQuot P.gens) 1) hl
    rw [Submodule.map_smul''] at key
    convert key using 1
    have e : MonoidAlgebra.single (g * v) (1 : B) = MonoidAlgebra.single g 1 * MonoidAlgebra.single v 1 := by
      rw [MonoidAlgebra.single_mul_single, mul_one]
    rw [hs, hs, TensorProduct.mk_apply, e, map_mul, mul_sub, mul_one, TensorProduct.tmul_sub]
