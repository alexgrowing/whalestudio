import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIdem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ChartValJ
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ModuliUnivEtaKilled
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsPowMulCoprimeLe
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTranslationSectionsUniversalObject
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatRootsStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatFullLinearLevelStructureStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsotropicGroupLatticeClassRepresentativesStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatSplitIsotropicGroup
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.RatData

theorem epi_spMap_fields {K L : Type} [Field K] [Field L] (i : K →+* L) : Epi (spMap i) := by
  have : Flat (spMap i) := by
    rw [spMap, Flat.SpecMap_iff]
    exact RingHom.Flat.of_isField (Field.toIsField K) _
  have : Surjective (spMap i) := ⟨Function.surjective_to_subsingleton _⟩
  exact Flat.epi_of_flat_of_surjective _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem cancel_of_left_eq (Xo : Moduli Dw l) {K L : Type} [Field K] [Field L] {x : Sp K ⟶ Xo.X} {x' : Sp L ⟶ Xo.X}
    (i : K →+* L) (g : ptO Xo x' ⟶ ptO Xo x) (hg : g.left = spMap i) {a b : ptO Xo x ⟶ Xo.univ.t.G}
    (h : g ≫ a = g ≫ b) : a = b := by
  have := epi_spMap_fields i
  have h₁ := congrArg (fun f => f.left) h
  simp only [Over.comp_left, hg] at h₁
  ext1
  exact (cancel_epi (spMap i)).1 h₁

theorem descend (Xo : Moduli Dw l) {K : Type} [Field K] (x : Sp K ⟶ Xo.X) (M : ℕ) (hx : AllRat Xo x M)
    {B : Type} [CommRing B] (φ : K →+* B) (hφ : φ.FaithfullyFlat) :
    ∃ (Ω : Type) (_ : Field Ω) (χ : B →+* Ω) (x' : Sp Ω ⟶ Xo.X) (g₁ : ptO Xo x' ⟶ ptO Xo (spMap φ ≫ x))
      (g₂ : ptO Xo x' ⟶ ptO Xo x), g₁.left = spMap χ ∧ g₂.left = spMap (χ.comp φ) ∧ g₂.left = g₁.left ≫ spMap φ ∧
      ∀ w : ptO Xo (spMap φ ≫ x) ⟶ Xo.univ.t.G, w ^ M = 1 → ∃ a, g₂ ≫ a = g₁ ≫ w := by
  have : Nontrivial B := hφ.injective.nontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  let χ : B →+* B ⧸ m := Ideal.Quotient.mk m
  have hc : spMap (χ.comp φ) = spMap χ ≫ spMap φ := by
    rw [spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  let g₁ : ptO Xo (spMap (χ.comp φ) ≫ x) ⟶ ptO Xo (spMap φ ≫ x) :=
    Over.homMk (spMap χ) (by
      change spMap χ ≫ spMap φ ≫ x = spMap (χ.comp φ) ≫ x
      rw [hc, Category.assoc])
  let g₂ : ptO Xo (spMap (χ.comp φ) ≫ x) ⟶ ptO Xo x := Over.homMk (spMap (χ.comp φ)) rfl
  refine ⟨B ⧸ m, inferInstance, χ, _, g₁, g₂, rfl, rfl, hc, fun w hw => ?_⟩
  obtain ⟨a, ha⟩ := hx (B ⧸ m) (χ.comp φ) (g₁ ≫ w) (by rw [← MonObj.comp_pow, hw, MonObj.comp_one])
  exact ⟨a, Over.OverMorphism.ext ha.symm⟩

theorem exists_root (Xo : Moduli Dw l) {K : Type} [Field K] (x : Sp K ⟶ Xo.X) (N : ℕ) (hN : 0 < N)
    (hx : AllRat Xo x (N ^ 2)) (t : ptO Xo x ⟶ Xo.univ.t.G) (ht : t ^ N = 1) : ∃ r, r ^ N = t := by
  obtain ⟨B, _, φ, w, hφ, hw⟩ := GlobalTheory.T.exists_faithfullyFlat_nthRoots_of_torsion GlobalTheory.firstFiveLaws.1 E H Dw l Xo K x N N hN hN Unit
    (fun _ => t) (fun _ => ht)
  obtain ⟨Ω, _, χ, x', g₁, g₂, h₁, h₂, h₃, h₄⟩ := descend Xo x _ hx φ hφ
  let g : ptO Xo (spMap φ ≫ x) ⟶ ptO Xo x := Over.homMk (spMap φ) rfl
  have hw' : w () ^ N = g ≫ t := Over.OverMorphism.ext (hw ())
  have hg : g₂ = g₁ ≫ g := Over.OverMorphism.ext h₃
  obtain ⟨a, ha⟩ := h₄ (w ()) (by rw [pow_two, pow_mul, hw', ← MonObj.comp_pow, ht, MonObj.comp_one])
  refine ⟨a, cancel_of_left_eq Xo _ g₂ h₂ ?_⟩
  rw [MonObj.comp_pow, ha, ← MonObj.comp_pow, hw', hg, Category.assoc]

theorem exists_linear_level (Xo : Moduli Dw l) {K : Type} [Field K] (x : Sp K ⟶ Xo.X) (k : ℕ) (hk : 0 < k)
    (hx : AllRat Xo x k) : ∃ ev : Dw.La → (ptO Xo x ⟶ Xo.univ.t.G), (∀ a b, ev (a + b) = ev a * ev b) ∧
      (∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ Xo.univ.t.act.act o) ∧ (∀ a, ev (k • a) = 1) ∧
      ∀ a b, ev a = ev b → Dw.ModN k (a - b) := by
  obtain ⟨B, _, φ, ev, hφ, hadd, hsm, hkill, hinj⟩ := GlobalTheory.T.exists_faithfullyFlat_full_linear_level_structure GlobalTheory.firstFiveLaws.1 E H Dw l Xo K x k hk
  obtain ⟨Ω, _, χ, x', g₁, g₂, h₁, h₂, -, h₄⟩ := descend Xo x _ hx φ hφ
  choose e he using fun a => h₄ (ev a) (by rw [← map_nsmul_eq_pow_of_add_eq_mul ev hadd, hkill])
  refine ⟨e, fun a b => cancel_of_left_eq Xo _ g₂ h₂ ?_, fun o a => cancel_of_left_eq Xo _ g₂ h₂ ?_,
    fun a => cancel_of_left_eq Xo _ g₂ h₂ ?_, fun a b hab => hinj Ω χ a b ?_⟩
  · rw [MonObj.comp_mul, he, he, he, hadd, MonObj.comp_mul]
  · rw [← Category.assoc, he, he, hsm, Category.assoc]
  · rw [he, hkill, MonObj.comp_one, MonObj.comp_one]
  · have h : g₁ ≫ ev a = g₁ ≫ ev b := by rw [← he, ← he, hab]
    have h' := congrArg (fun f => f.left) h
    simp only [Over.comp_left, h₁] at h'
    exact h'

theorem exists_thetaVal_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), (AllRat Xo y.x (l.M ^ 2) → ∀ x : Dw.La, ∃ F, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y.s (levPt Xo y.x x) F) ∧ ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.LevOK N l.M → AllRat Xo y.x (N ^ 2) → ∃ (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (tp : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (F : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))), (∀ i, InZh Xo Λ N (z i)) ∧ GeoInj Xo y.x z ∧ (∀ q b, tp q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp q b)) ∧ (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z i b) (tp q b) (F q i b)) := by
  intro E _ _ _ H Dw l Xo c K _ _ y
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hM : 0 < l.M := l.odd.pos
  have hlev : ∀ a : Dw.La, KilledBy Xo l.Mb (levPt Xo y.x a) ∧ levPt Xo y.x a ^ l.M = 1 := by
    intro a
    obtain ⟨h₁, -, h₃⟩ := moduli_univ_eta_killed hL E H Dw l Xo a
    refine ⟨fun b hb => ?_, ?_⟩
    · rw [levPt, Category.assoc, h₁ b hb, MonObj.comp_one]
    · rw [levPt, ← MonObj.comp_pow, h₃, MonObj.comp_one]
  refine ⟨fun hx a => ?_, fun n Λ N hU hLev hx => ?_⟩
  · obtain ⟨v, hv⟩ := exists_root Xo y.x l.M hM hx _ (hlev a).2
    obtain ⟨t', ht', hk⟩ := (exists_root_killedBy_pow E H Dw l Xo _ _ v l.M hM (hlev a).1 hv).2 rfl
    refine (exists_isVtOver_and_existsUnique_isUUOver hL E H Dw l Xo l.M l.odd (ptO Xo y.x) y.s).1 _ _ t' ht' ?_ hk
    rw [pow_two, pow_mul, ht', (hlev a).2]
  · obtain ⟨hodd, hdvd, hle⟩ := hLev
    have hN : 0 < N := hodd.pos
    have hlevN : ∀ a : Dw.La, levPt Xo y.x a ^ N = 1 := by
      intro a
      obtain ⟨k, hk⟩ := hdvd
      rw [hk, pow_mul, (hlev a).2, one_pow]
    choose r hr using fun q : LevQ Dw l => exists_root Xo y.x N hN hx _ (hlevN (levRep q))
    choose t ht ht' using fun q =>
      (exists_root_killedBy_pow E H Dw l Xo _ _ _ N hN (hlev _).1 (hr q)).1
    have htN : ∀ q, t q ^ (N ^ 2) = 1 := fun q => by rw [pow_two, pow_mul, ht q, hlevN]
    obtain ⟨ev, hadd, hsm, hk, hinj⟩ := exists_linear_level Xo y.x (N ^ 2) (pow_pos hN 2) hx
    obtain ⟨zz, hz, hzi, -⟩ := GlobalTheory.T.exists_isotropic_group_lattice_class_representatives E H Dw n Λ N hU hN (hle.trans inf_le_left)
    have hZ : ∀ i, InZh Xo Λ N (fun b => ev (zz i b)) := by
      refine fun i => ⟨fun b => ?_, ?_⟩
      · rw [← map_nsmul_eq_pow_of_add_eq_mul ev hadd, hk]
      · intro mu hmu cm hcm i'
        obtain ⟨u, hu⟩ := hz i mu hmu cm hcm i'
        simp only [← hsm]
        rw [← map_sum_eq_prod_ofFn_of_add_eq_mul ev hadd, hu]
        exact hk u
    choose F hF using fun (q : Fin n → LevQ Dw l) i b =>
      ((exists_isVtOver_and_existsUnique_isUUOver hL E H Dw l Xo N hodd _ y.s).2 (ev (zz i b)) (t (q b))
        ((hZ i).1 b) (htN _)).exists
    refine ⟨fun i b => ev (zz i b), fun q b => t (q b), F, hZ, ?_, fun q b => ⟨ht _, ht' _⟩, hF⟩
    intro k _ ψ g hg i i' hii
    exact hzi _ _ fun b => hinj _ _ (cancel_of_left_eq Xo ψ g hg (congrFun hii b))

end GlobalTheory.RatData
