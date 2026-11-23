import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LiftUnit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.OEpsEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ODownEx
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsGenericModuliPoint
import Development.AutomorphicArithmetic.CommutativeAlgebra.LatticeGeneration
import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientModuliObjectExists
import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientMapComp
import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientUniqueOfComp
import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientModuliIso
import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientLevelOfLatticeGeneration
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsogenyClassExistsOfQuotient
import Development.AutomorphicArithmetic.CommutativeAlgebra.TraceEtaIdentity
import Development.AutomorphicArithmetic.CommutativeAlgebra.MultiplierIsUnit
import Development.AutomorphicArithmetic.CommutativeAlgebra.TracePullbackIdentity
import Development.AutomorphicArithmetic.CommutativeAlgebra.TraceUnitOfPullbackMultiplier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPosOfCoprime

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.FiniteEtaleModels.O

set_option maxHeartbeats 400000 in
private theorem stepF_of (hGen : GenEx) (hComp : QComp) (hIso : QIso) (hCls : ClsEx) (hEta : TrEta) (hUnit : TrUnit)
    (hEps : EpsEx) (hDown : DownEx) : UpperTheory.Gal.FiniteEtaleModels.StepF := by
  intro p _ D G L hSc E _ _ gb w q _ r 𝔴 𝔫 S k T N₀ κ 𝔟₁ 𝔟₂ X₁ X₂ hle M₁ M₂ c₁ c₂ a₁ a₂ hN₁ hN₂ hM C₁ C₂ W
  obtain ⟨hM₁, hg₁⟩ := hN₁
  obtain ⟨hM₂, hg₂⟩ := hN₂
  obtain ⟨t, ht⟩ := hM
  have hM₁' : (M₁ : ℕ) = N₀ * κ * c₁ := hM₁
  have hM₂' : (M₂ : ℕ) = N₀ * c₂ := hM₂
  have hpos : 0 < (M₁ : ℕ) := by have := M₁.2.1; omega
  obtain ⟨h3, hcq₂, -, -, -⟩ := X₂.lev
  obtain ⟨-, hcq₁, -, -, -⟩ := X₁.lev
  have hN₀pos : 0 < N₀ := by omega
  have hd : N₀ ∣ N₀ * κ := dvd_mul_right N₀ κ
  obtain ⟨ε, hdvd, hεid⟩ := hEps (𝓞 D.F) 𝔟₁ 𝔟₂ a₁ a₂ M₁ M₂ t hpos ht hle hg₁ hg₂
  obtain ⟨τ, m, hτ, hfin, het, hml⟩ :=
    hDown p D hSc.m1 hSc.a1 E gb w q r 𝔴 𝔫 S N₀ κ 𝔟₁ 𝔟₂ X₁ X₂ ε hεid
  have hcart : IsGrpPullback (T.M M₁).univ.A (X₁.Y.univ.forget N₀ hd hcq₁).A C₁.j C₁.m.φ := C₁.m.cart
  have hsq : Geo.Tor.IsSquare C₁.m.φ C₁.m.φ₂ := C₁.m.sq
  have hact : ∀ x, Over.Hom.left ((T.M M₁).univ.act.act x) ≫ C₁.m.φ =
      C₁.m.φ ≫ Over.Hom.left ((X₁.Y.univ.forget N₀ hd hcq₁).act.act x) := C₁.m.act
  have hpol : LBIso (T.M M₁).univ.P ((X₁.Y.univ.forget N₀ hd hcq₁).P.pull C₁.m.φ₂) := C₁.m.pol
  have heF : ∀ y : D.La, Over.Hom.left ((T.M M₁).univ.eta ((c₁ * κ) • y)) ≫ C₁.m.φ =
      C₁.j ≫ Over.Hom.left ((X₁.Y.univ.forget N₀ hd hcq₁).eta y) := by
    intro y
    rw [Obj.forget_eta, Nat.mul_div_cancel_left κ hN₀pos, mul_smul]
    exact C₁.m.eta (κ • y)
  obtain ⟨nF, hnFφ⟩ : ∃ n : @QMap q _ (datAt S.atq S.sp) (Ow w) E _ _ _ S.b gb _ _ X₁.Y.s (T.M M₁).s _ _
      (T.M M₁).univ (X₁.Y.univ.forget N₀ hd hcq₁) C₁.j (c₁ * κ), n.φ = C₁.m.φ :=
    ⟨⟨C₁.m.φ, C₁.m.φ₂, hcart, hsq, hact, hpol, heF⟩, rfl⟩
  obtain ⟨nA, hnA⟩ := (hComp q (datAt S.atq S.sp) (Ow w) E S.b gb (M₁ : ℕ) N₀ (c₁ * κ) (T.M M₁).X X₁.Y.X
    X₂.Y.X (T.M M₁).s X₁.Y.s X₂.Y.s (T.M M₁).univ (X₁.Y.univ.forget N₀ hd hcq₁) X₂.Y.univ C₁.j τ).1 nF m
  obtain ⟨n₂, hn₂⟩ := (hComp q (datAt S.atq S.sp) (Ow w) E S.b gb (M₂ : ℕ) N₀ c₂ (T.M M₂).X X₂.Y.X
    X₂.Y.X (T.M M₂).s X₂.Y.s X₂.Y.s (T.M M₂).univ X₂.Y.univ X₂.Y.univ C₂.j (𝟙 _)).2.2.2
    (T.M M₁).X (T.M M₁).s W.o W.π W.φ C₂.m
  obtain ⟨hiso, hpol'⟩ :=
    hUnit p D G L E gb 1 (T.M M₁).X (T.M M₁).s M₁ M₂ (T.M M₁).univ W.o W.ψ W.trans (one_mem _)
  have hex : ∀ (n : ℕ) (x : D.La), ∃ v ∈ LaHat D, (L.actG 1) (inAf D x) = inAf D x + n • v :=
    fun n x => ⟨0, zero_mem _, by simp⟩
  have heta₁ : ∀ y : D.La, (T.M M₁).univ.eta ((c₁ * κ) • y) ≫ W.ψ = W.o.eta (c₂ • y) :=
    fun y => hEta p D G L E gb 1 (T.M M₁).X (T.M M₁).s M₁ M₂ (T.M M₁).univ W.o W.ψ W.trans N₀ (c₁ * κ) c₂
      (by rw [hM₁']; ring) hM₂' y y (hex N₀ y)
  obtain ⟨nB, hnB⟩ := hIso q (datAt S.atq S.sp) (Ow w) E S.b gb (M₂ : ℕ) (M₁ : ℕ) N₀ c₂ (c₁ * κ) (T.M M₁).X
    X₂.Y.X (T.M M₁).s X₂.Y.s (T.M M₁).univ W.o X₂.Y.univ (W.π ≫ C₂.j) W.ψ hiso W.trans.1 W.trans.2.1 hpol'
    heta₁ n₂
  have heq : ∀ y : D.La, (T.M M₁).univ.eta ((algebraMap (𝓞 D.F) D.O) ((t : 𝓞 D.F) * a₂) • y) =
      (T.M M₁).univ.eta ((algebraMap (𝓞 D.F) D.O) (a₁ * ε) • y) := by
    intro y
    obtain ⟨z, hz⟩ := hdvd
    have e1 : (algebraMap (𝓞 D.F) D.O) (a₁ * ε) • y = (algebraMap (𝓞 D.F) D.O) ((t : 𝓞 D.F) * a₂) • y +
        (M₁ : ℕ) • ((algebraMap (𝓞 D.F) D.O) z • y) := by
      have h' : a₁ * ε = (t : 𝓞 D.F) * a₂ + ((M₁ : ℕ) : 𝓞 D.F) * z := by linear_combination hz
      rw [h', map_add, add_smul, map_mul (algebraMap (𝓞 D.F) D.O) ((M₁ : ℕ) : 𝓞 D.F) z, mul_smul,
        map_natCast, Nat.cast_smul_eq_nsmul]
    have h1 := (T.M M₁).univ.eta_add ((algebraMap (𝓞 D.F) D.O) ((t : 𝓞 D.F) * a₂) • y)
      ((M₁ : ℕ) • ((algebraMap (𝓞 D.F) D.O) z • y))
    have h2 := (T.M M₁).univ.eta_ker ((algebraMap (𝓞 D.F) D.O) z • y)
    rw [e1]
    refine (h1.trans ?_).symm
    exact (congrArg (_ * ·) h2).trans (_root_.mul_one _)
  have hkey : ∀ y : D.La, (T.M M₁).univ.eta ((algebraMap (𝓞 D.F) D.O) ((t : 𝓞 D.F) * a₂) • y) ≫ W.ψ =
      W.o.eta ((algebraMap (𝓞 D.F) D.O) a₂ • y) := by
    intro y
    have h' := hEta p D G L E gb 1 (T.M M₁).X (T.M M₁).s M₁ M₂ (T.M M₁).univ W.o W.ψ W.trans M₂ t 1 ht
      (_root_.mul_one _).symm ((algebraMap (𝓞 D.F) D.O) a₂ • y) ((algebraMap (𝓞 D.F) D.O) a₂ • y) (hex _ _)
    rw [map_mul, mul_smul, map_natCast, Nat.cast_smul_eq_nsmul, h', one_smul]
  have lvA : ∀ y : D.La, Over.Hom.left ((T.M M₁).univ.eta ((algebraMap (𝓞 D.F) D.O) ((t : 𝓞 D.F) * a₂) • y)) ≫ nA.φ =
      (C₁.j ≫ τ) ≫ Over.Hom.left (X₂.Y.lv y) := by
    intro y
    rw [heq, hnA, hnFφ, map_mul, mul_smul]
    exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ m.φ) (C₁.lv _))).trans
      ((Category.assoc _ _ _).trans ((congrArg (C₁.j ≫ ·) (hml y)).trans (Category.assoc _ _ _).symm))
  have lvB : ∀ y : D.La, Over.Hom.left ((T.M M₁).univ.eta ((algebraMap (𝓞 D.F) D.O) ((t : 𝓞 D.F) * a₂) • y)) ≫ nB.φ =
      (W.π ≫ C₂.j) ≫ Over.Hom.left (X₂.Y.lv y) := by
    intro y
    rw [hnB, hn₂, ← Category.assoc, ← Over.comp_left, hkey, ← Category.assoc]
    exact (congrArg (· ≫ C₂.m.φ) (W.φ.eta _)).trans ((Category.assoc _ _ _).trans
      ((congrArg (W.π ≫ ·) (C₂.lv y)).trans (Category.assoc _ _ _).symm))
  obtain ⟨CA, hCAj, hCAm⟩ : ∃ C : @Cls q _ (datAt S.atq S.sp) (Ow w) E _ _ _ S.b gb (T.M M₁).X (T.M M₁).s
      (M₁ : ℕ) N₀ 𝔟₂ X₂.Y (algebraMap (Ow w) E) (T.M M₁).univ (c₁ * κ) ((t : 𝓞 D.F) * a₂),
      C.j = C₁.j ≫ τ ∧ C.m.φ = nA.φ :=
    ⟨⟨C₁.j ≫ τ, (Category.assoc _ _ _).trans ((congrArg (C₁.j ≫ ·) hτ).trans C₁.ov), nA, lvA⟩, rfl, rfl⟩
  obtain ⟨CB, hCBj, hCBm⟩ : ∃ C : @Cls q _ (datAt S.atq S.sp) (Ow w) E _ _ _ S.b gb (T.M M₁).X (T.M M₁).s
      (M₁ : ℕ) N₀ 𝔟₂ X₂.Y (algebraMap (Ow w) E) (T.M M₁).univ (c₁ * κ) ((t : 𝓞 D.F) * a₂),
      C.j = W.π ≫ C₂.j ∧ C.m.φ = nB.φ :=
    ⟨⟨W.π ≫ C₂.j, (Category.assoc _ _ _).trans ((congrArg (W.π ≫ ·) C₂.ov).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ spMap _) W.ov))), nB, lvB⟩, rfl, rfl⟩
  have hgen : IsGen ((t : 𝓞 D.F) * a₂) (M₁ : ℕ) 𝔟₂ := by
    rw [ht]
    exact (hGen (𝓞 D.F) 𝔟₂ M₂ (by have := M₂.2.1; omega)).2 a₂ t hg₂
  obtain ⟨hj, hφ⟩ := (hCls q (datAt S.atq S.sp) (Ow w) E S.b gb (algebraMap (Ow w) E) S.mat (M₁ : ℕ) N₀
    (c₁ * κ) ((t : 𝓞 D.F) * a₂) 𝔟₂ (by rw [hM₁']; ring) hpos h3 hcq₂ hgen X₂.Y (T.M M₁).X (T.M M₁).s
    (T.M M₁).univ).2 CA CB
  rw [hCAj, hCBj] at hj
  rw [hCAm, hCBm, hnA, hnB, hn₂, hnFφ] at hφ
  exact ⟨⟨τ, hτ, m.φ, m.cart.1.w⟩, ⟨hj, hφ⟩, hfin, het, m.cart.1⟩

theorem stepF : UpperTheory.Gal.FiniteEtaleModels.StepF :=
  stepF_of UpperTheory.exists_generic_moduli_point UpperTheory.quotient_map_comp UpperTheory.quotient_moduli_iso
    (UpperTheory.isogeny_class_exists_of_quotient UpperTheory.quotient_moduli_object_exists UpperTheory.quotient_map_comp (UpperTheory.quotient_unique_of_comp UpperTheory.quotient_map_comp) (UpperTheory.quotient_level_of_lattice_generation UpperTheory.lattice_generation))
    UpperTheory.trace_eta_identity (UpperTheory.trace_unit_of_pullback_multiplier UpperTheory.trace_pullback_identity UpperTheory.multiplier_is_unit) epsEx downEx

end UpperTheory.Gal.FiniteEtaleModels.O
