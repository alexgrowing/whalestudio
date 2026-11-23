import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreExistsGeneratorStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaConstantListOfFibrePullbackFieldExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasThetaConstantsTwoLevelsMoveCartesian
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasTh
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.SymAtOfThList
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThNe

variable {S : Scheme.{0}}

theorem ptSecT_translT_mulT {A : Over S} [GrpObj A] (T : Over S) (y : T ⟶ A) (m : ℕ) :
    ptSecT A (1 : T ⟶ A) ≫ translT A y ≫ mulT A T m = ptSecT A (y ^ m) := by
  have e : ptSecT A (1 : T ⟶ A) ≫ translT A y = ptSecT A y := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [ptSecT, translT]
    · simp only [ptSecT, translT, translPt, Category.assoc, lift_snd, Hom.mul_def, comp_lift_assoc, lift_fst_assoc,
        Category.id_comp]
      rw [← Hom.mul_def, _root_.mul_one]
  rw [← Category.assoc, e]
  apply CartesianMonoidalCategory.hom_ext
  · simp [ptSecT, mulT]
  · simp only [ptSecT, mulT, lift_snd, Category.assoc]
    rw [MonObj.comp_pow, lift_snd]

theorem ne_zero_of_thG {K : Type} [Field K] {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    {ρ : LB.Gen (L.pull (eSec A))} {m : ℕ} {t : Sp K ⟶ S} {th : LB.Sec (LPow A L ((1 : ℕ) : ℤ) (Over.mk t))}
    {y : Over.mk t ⟶ A} {c : K} (H : ThG A L ρ m th y (fn c))
    (hu : ∀ z J, Good L z J → IsUnit (VVRank.sv A th (ptSecT A (y ^ m)).left z J)) : c ≠ 0 := by
  intro hc
  obtain ⟨-, t', α, s₁, θ, -, -, hs₁, hθ, ht, hc'⟩ := H
  obtain ⟨z⟩ : Nonempty (Sp K) := inferInstance
  obtain ⟨J, hJ, -⟩ := exists_good L hL z (K := Empty) Empty.elim Empty.elim (fun a => a.elim) (fun k => k.elim)
  have q := hc' z J hJ
  have a1 := VVRank.sv_of_isTwistPull A ht (ptSecT A 1).left z hJ
  have a2 := VVRank.sv_of_isTwistPull A hs₁ ((ptSecT A 1).left ≫ (translT A θ.pt).left) z hJ
  have e : ((ptSecT A (1 : Over.mk t ⟶ A)).left ≫ (translT A θ.pt).left) ≫ (mulT A (Over.mk t) m).left =
      (ptSecT A (y ^ m)).left := by
    rw [hθ.pt_eq, ← Over.comp_left, ← Over.comp_left, Category.assoc, ptSecT_translT_mulT]
  rw [e] at a2
  rw [a2] at a1
  have f0 : (fn (0 : K) : Γ((Over.mk t).left, ⊤)) = 0 := map_zero _
  rw [hc, f0, gs_eq _ z ⊤ trivial, map_zero, map_zero, zero_mul] at q
  have q2 := a1.symm.trans q
  rw [Units.mul_right_eq_zero, Units.mul_right_eq_zero] at q2
  exact (hu z J hJ).ne_zero q2

theorem exists_pow_eq_of_card {G : Type} [CommGroup G] {m g : ℕ} (hm : 0 < m)
    (h1 : Nat.card {x : G // x ^ m = 1} = m ^ (2 * g)) (h2 : Nat.card {x : G // x ^ (m ^ 2) = 1} = (m ^ 2) ^ (2 * g))
    (x : G) (hx : x ^ m = 1) : ∃ y : G, y ^ (m ^ 2) = 1 ∧ y ^ m = x := by
  let H2 := (powMonoidHom (m ^ 2) : G →* G).ker
  let H1 := (powMonoidHom m : G →* G).ker
  let f : H2 →* G := (powMonoidHom m).comp H2.subtype
  have cH2 : Nat.card H2 = (m ^ 2) ^ (2 * g) := h2 ▸ Nat.card_congr (Equiv.subtypeEquivRight fun y => by simp [H2])
  have cH1 : Nat.card H1 = m ^ (2 * g) := h1 ▸ Nat.card_congr (Equiv.subtypeEquivRight fun y => by simp [H1])
  have cK : Nat.card f.ker = m ^ (2 * g) := by
    rw [← h1]
    refine Nat.card_congr
      { toFun := fun y => ⟨y.1.1, MonoidHom.mem_ker.1 y.2⟩
        invFun := fun x => ⟨⟨x.1, by simp [H2, pow_two, pow_mul, x.2]⟩, MonoidHom.mem_ker.2 x.2⟩
        left_inv := fun y => rfl
        right_inv := fun x => rfl }
  have hpos : 0 < m ^ (2 * g) := pow_pos hm _
  haveI : Finite H2 := Nat.finite_of_card_ne_zero (by rw [cH2]; positivity)
  haveI : Finite H1 := Nat.finite_of_card_ne_zero (by rw [cH1]; positivity)
  have cR : Nat.card f.range = m ^ (2 * g) := by
    have e := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker, cK, cH2, show (m ^ 2) ^ (2 * g) = m ^ (2 * g) * m ^ (2 * g) by ring] at e
    exact Nat.eq_of_mul_eq_mul_left hpos e
  have hle : f.range ≤ H1 := by
    rintro _ ⟨y, rfl⟩
    have := y.2
    simp only [H2, MonoidHom.mem_ker, powMonoidHom_apply] at this
    simp [H1, f, ← pow_mul, ← pow_two, this]
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [cH1, cR])
  have hx1 : x ∈ H1 := by simpa [H1] using hx
  rw [← heq] at hx1
  obtain ⟨y, hy⟩ := hx1
  exact ⟨y.1, MonoidHom.mem_ker.1 y.2, hy⟩

end GlobalTheory.UMin.ThNe

namespace GlobalTheory.UMin.ThNe

theorem spMap_id_self (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _

theorem th_ne_zero : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left)
    (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (K : Type) [Field K] (x : Sp K ⟶ S)
    (c : Fin N → K), Odd m → 3 ≤ m → (m : K) ≠ 0 → PolFib G L g x → HasTh G L ρ m x c → ∃ a, c a ≠ 0 := by
  intro S G _ _ L ρ hL hρ g m N K _ x c hm hm3 hmK hpol H
  obtain ⟨hLaws, hLaws2⟩ := abelianSchemeLaws_all
  obtain ⟨P, α, -, hα, hPL⟩ := hpol
  haveI := P.isAb.comm
  obtain ⟨ρ', hρ'⟩ := P.rigid
  have H' : HasTh P.A P.L ρ' m (𝟙 (Sp K)) c := by
    rw [hasTh_iff] at H ⊢
    exact (ThMove.hasTh₂_move S G L ρ hL hρ (Sp K) P.A P.L ρ' x α P.isLB hρ' hα hPL m m N N K (𝟙 _) c c).2
      (by rwa [Category.id_comp])
  obtain ⟨θ, pt, hgθ, hl⟩ := H'
  let i : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  obtain ⟨pt', -, hl'⟩ := GlobalTheory.T.isThetaConstantListOfFibre_pullback_field_extension (Sp K) P.A P.L ρ' P.isLB hρ' m N K (AlgebraicClosure K) i (𝟙 _) θ pt c hl
  have hg' : IsGenSec P.A P.L _ (SecAt.pull P.A P.L θ i) :=
    (gen_of_polFib (Sp K) P.A P.L P.isLB P.g K (𝟙 _) (Model.polFib_self P)).2 θ hgθ (AlgebraicClosure K) i
  have hne := ThetaCoset.ne_zero_of_isGenSec hLaws2.secBaseChangeAny P (spMap i ≫ 𝟙 (Sp K)) hg'
  have hmKb : (m : AlgebraicClosure K) ≠ 0 := by
    rw [← map_natCast i]; exact (map_ne_zero i).2 hmK
  obtain ⟨z, hz, hu⟩ := UT.ExactTerm.exists_good_point hLaws.goodPt hLaws.polBaseChange P (spMap i ≫ 𝟙 (Sp K))
    (n := m) (by omega) hmKb _ hne 1
  have c1 := (hLaws.mulN (Sp K) P m (by omega)).2.2.2.2 (AlgebraicClosure K) (spMap i ≫ 𝟙 (Sp K)) hmKb
  have c2 := (hLaws.mulN (Sp K) P (m ^ 2) (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (by omega)))).2.2.2.2
    (AlgebraicClosure K) (spMap i ≫ 𝟙 (Sp K)) (by push_cast; exact pow_ne_zero _ hmKb)
  obtain ⟨y, hy2, hym⟩ := exists_pow_eq_of_card (by omega) c1 c2 (1 * z) (by rw [_root_.one_mul, hz])
  let π : Over.mk (spMap (RingHom.id (AlgebraicClosure K)) ≫ spMap i ≫ 𝟙 (Sp K)) ⟶ Over.mk (spMap i ≫ 𝟙 (Sp K)) :=
    Over.homMk (spMap (RingHom.id (AlgebraicClosure K))) rfl
  obtain ⟨a, ha⟩ := hl'.2.2 (AlgebraicClosure K) (RingHom.id _) (π ≫ y)
    (by rw [← MonObj.comp_pow, hy2, MonObj.comp_one])
  have hya : y = pt' a := by
    apply Over.OverMorphism.ext
    have := ha
    simp only [π, Over.comp_left, Over.homMk_left] at this
    rwa [spMap_id_self, Category.id_comp, Category.id_comp] at this
  refine ⟨a, fun h0 => ?_⟩
  have hth := hl'.2.1 a
  rw [← hya] at hth
  refine ne_zero_of_thG P.isLB hth (fun p J hJ => ?_) (by show i (c a) = 0; rw [h0, map_zero])
  rw [hym]
  exact hu p J hJ

end GlobalTheory.UMin.ThNe
