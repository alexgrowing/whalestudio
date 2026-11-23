import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsOfDouble
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondOfEigenbasis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueSumSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLieBasisOfHolUnif
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTateIsoOfPeriods

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open PeriodPoint

theorem exists_point_of_period : ThetaUnifAV → Out.Laws → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M
    : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → (∀ (g : ℕ) (Λ : Submodule ℤ (Fin
    g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (Ef
    : LinearMap.BilinForm ℤ Λ), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g →
    ℂ)) = ⊤ → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ a b : Λ, (Ef
    a b : ℝ) = (hermForm Hm a b).im) → Function.Bijective Ef → ∃ (P : Out.PolAV (Sp ℂ)) (u
    : HolUnif P.A P.L g) (χ
    : u.Λ → ℂ), P.g = g ∧ u.Λ = Λ ∧ u.IsAH Hm χ ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v)) → (∀ (P
    P' : Out.PolAV (Sp ℂ)) (g : ℕ) (u : HolUnif P.A P.L g) (u' : HolUnif P'.A P'.L g) (F : (Fin g →
    ℂ) →ₗ[ℂ] (Fin g →
    ℂ)), P.g = g → P'.g = g → (∀ z ∈ u.Λ, F z ∈ u'.Λ) → ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u'.ex (F
    z) = u.ex z ≫ f) → (∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (P : Out.PolAV (Sp
    k)) (a a' : P.A ⟶ P.A), IsMonHom a → IsMonHom a' → (∀ (n : ℕ) (x y : 𝟙_ (Over (Sp k)) ⟶ P.A) (c
    : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ), 0 < n → x ^ n = 1 → y ^ n = 1 → Out.WeilIs P.A P.L n (x ≫
    a) y c → Out.WeilIs P.A P.L n x (y ≫ a') c) → LBIso (cubeLB P.A ![fst P.A P.A ≫ a, snd P.A P.A]
    P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ a'] P.L)) → (∀ (E : Type) [Field E] [NumberField
    E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B] (act
    : OAct (𝓞 E) B) (M : LB B.left), IsAbelianScheme B → M.IsLB → (∃ t : LB.Gen (Theta B
    M), t.IsGen) → (∀ a, LBIso (cubeLB B ![fst B B ≫ act.act a, snd B B] M) (cubeLB B ![fst B B, snd
    B B ≫ act.act (H.bar a)] M)) → ∃ (PP : RigLB B) (_
    : CubicalStr B PP), PP.IsSymmetric ∧ LBIso PP.L (cubeLB B ![𝟙 B, act.act H.w0]
    M) ∧ LBIso (abelian₂ B PP.L) (abelian₂ B M) ∧ LBIso PP.L (cubeLB B ![𝟙 B, act.act H.w0]
    PP.L) ∧ ∀ a, LBIso (cubeLB B ![fst B B ≫ act.act a, snd B B] PP.L) (cubeLB B ![fst B B, snd B B
    ≫ act.act (H.bar a)] PP.L)) → (∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (P
    : Out.PolAV (Sp k)) (n : ℕ) (B : Over (Sp k)) [GrpObj B] (ψ : P.A ⟶ B) (M
    : LB B.left), 0 < n → IsAbelianScheme B → M.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → Nat.card {x
    : 𝟙_ (Over (Sp k)) ⟶ P.A // x ≫ ψ = 1} = n ^ P.g → LBIso (abelian₂ P.A (lbPow P.L n)) (abelian₂
    P.A (M.pull ψ.left)) → Out.KTriv B M) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B
    : Over S) [GrpObj A] [GrpObj B] (ψ : A ⟶ B) (M : LB B.left) (n
    : ℕ), 0 < n → IsAbelianScheme A → IsAbelianScheme B → M.IsLB → IsFinite ψ.left → (Out.RelAmple B
    M → Out.RelAmple A (M.pull ψ.left)) ∧ (Out.RelAmple B (lbPow M n) ↔ Out.RelAmple B M) ∧ (Flat
    ψ.left → Surjective ψ.left → Out.RelAmple A (M.pull ψ.left) → Out.RelAmple B
    M) ∧ ∀ M' : LB B.left, M'.IsLB → LBIso M M' → Out.RelAmple B M → Out.RelAmple B M') → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo
    : Moduli D l) (B : Type) [CommRing B] (b : Base l B) (j : KA l →+* B) (S : Scheme.{0}) (s
    : S ⟶ Sp B) (o : Obj D l b s), IsReduced S → j (baseKA l).ρ = b.ρ → j (baseKA
    l).ζ = b.ζ → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ f)) → ∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo
    : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA
    l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (P
    : D'.La →+ (Fin g → ℂ)), (D'.p = D.p ∧ D'.q = D.q ∧ ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν
    : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n *
    m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n
    : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧ σ (baseKA l).ζ = Complex.exp (-(2 * Real.pi *
    Complex.I) * (ν l.A : ℂ) / l.A) ∧ t = f l.M') → IsPeriod D' ty P → ∃ (y : Sp ℂ ⟶ Xo.X) (e : (Fin
    g → ℂ) → (Over.mk y ⟶ Xo.univ.t.G)), (y ≫ Xo.s = spMap σ ∧ IsPeriod D' ty P ∧ ((∀ z w, e (z +
    w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧
    (∀ w, ∃! v : epsPt y ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
    (∀ v : epsPt y ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e
    0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) ∧ (∀ z, e z = 1 ↔ z ∈ (P).range) ∧
    (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂
    : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ)
    / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P
    a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = e ((l.M : ℂ)⁻¹ • P (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = e ((l.A : ℂ)⁻¹ • P (t a))) := by
  intro _ laws cube tor hom adjW prim princ amp rep E _ _ _ H D l Xo σ g ty hpq hσ hty D' t P
    ⟨hp, hq, f, ν, htow, hiso, hsim, hζ, ht⟩ hP
  obtain ⟨T, L, u, hA, hdim, hamp, hK, ht₁, ht₂, hker, hact, hW⟩ :=
    exists_triple laws cube tor hom adjW prim princ amp D' ty P hP
  let Q : Out.PolAV (Sp ℂ) :=
    { A := T.G, isAb := hA, g := g, smoothDim := hdim, L := T.PP.L, isLB := T.PP.isLB,
      rigid := ⟨T.PP.rig, T.PP.rigGen⟩, sym := CechPic.sym_of_isSymmetric T.PP T.sym, ample := hamp, ktriv := hK }
  obtain ⟨v, hv, heig⟩ := exists_lieBasis_of_holUnif T.G L g u hA.smooth ht₁ ht₂
  have hmul : ∀ (n : ℕ) a, 0 < n → u.ex ((n : ℂ)⁻¹ • P (n • a)) = 1 := fun n a hn => by
    rw [hker, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ (Nat.cast_ne_zero.2 hn.ne')]
    exact ⟨a, rfl⟩
  have hadd : ∀ (n : ℕ) a b, u.ex ((n : ℂ)⁻¹ • P (f n (a + b))) =
      u.ex ((n : ℂ)⁻¹ • P (f n a)) * u.ex ((n : ℂ)⁻¹ • P (f n b)) := fun n a b => by
    rw [map_add, map_add, smul_add, u.ex_add]
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨κ, hκ₁, hκ₂, hκ₃⟩ := exists_halfLevel (D := D) l (fun a => u.ex ((l.M : ℂ)⁻¹ • P (f l.M a))) (hadd l.M)
    fun b => by rw [map_nsmul, hmul _ _ hM]
  let b : Base l ℂ :=
    { unit := fun n hn => IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn.ne')
      ρ := σ (baseKA l).ρ
      ρ_sq := by rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
      ζ := σ (baseKA l).ζ
      ζ_prim := (baseKA l).ζ_prim.map_of_injective σ.injective }
  let o : Obj D l b (𝟙 (Sp ℂ)) :=
    { t := T, proper := hA.proper, ample := hamp, ktriv := hK
      eta := κ, eta_add := hκ₁, eta_ker := hκ₂
      etaA := fun a => u.ex ((l.A : ℂ)⁻¹ • P (f l.A a))
      etaA_add := hadd l.A
      etaA_ker := fun a => by rw [map_nsmul, hmul _ _ l.A_pos]
      geom := fun k _ _ x β hx => by
        obtain rfl : x = spMap β := (Category.comp_id x).symm.trans hx
        refine ⟨?_, ?_⟩
        · rw [show b.ρ = H.rt0 from hσ]
          exact detCond_of_eigenbasis lieMult_of_eigenbasis D T ty hty v hv
            (fun i a => heig _ _ (T.act.hom a) (hact a) i) β
        · obtain ⟨I, hI₁, hI₂⟩ := exists_tateIso_of_periods laws E H D D' g ty P Q T.act u.ex f ν hpq hP u.ex_add
            u.ex_onto hker hact hW htow hiso hsim k β
          exact ⟨I, (hI₁ _).trans (congrArg β hζ.symm), fun a => (hI₂ _ a).symm,
            fun a ha => by rw [hκ₃ a ha]; exact (hI₂ _ a).symm⟩ }
  obtain ⟨y, ⟨hy, ⟨m⟩⟩, -⟩ := rep E H D l Xo ℂ b σ (Sp ℂ) (𝟙 _) o inferInstance rfl rfl
  obtain ⟨e, he, hhol, he₁, he₂, he₃⟩ := exists_fibre_unif T Xo.univ.t y m.toSABMap u ht₁ ht₂
  have hlev : ∀ n : ℕ, 0 < n → n ∣ l.M' → ∀ a, u.ex ((n : ℂ)⁻¹ • P (t a)) = u.ex ((n : ℂ)⁻¹ • P (f n a)) := by
    rintro n hn ⟨r, hr⟩ a
    have hr0 : 0 < r := Nat.pos_of_mul_pos_left ((Nat.lcm_pos hM l.A_pos).trans_eq hr)
    obtain ⟨c, hc⟩ := htow n r hn hr0 a
    rw [ht, hr, hc, map_add, smul_add, u.ex_add, hmul _ _ hn, _root_.mul_one]
  refine ⟨y, e, hy.trans (Category.id_comp _), hP, hhol, fun z => (he₁ z).trans (hker z),
    fun a z => he₂ a z _ (hact a z), fun k a a₂ c hk hc => he₃ k _ _ _ (hW k a a₂ c hk hc),
    fun a ha => Over.OverMorphism.ext ?_, fun a => Over.OverMorphism.ext ?_⟩
  · rw [he, hlev _ hM (Nat.dvd_lcm_left _ _), ← hκ₃ a ha]
    exact (m.eta a).symm
  · rw [he, hlev _ l.A_pos (Nat.dvd_lcm_right _ _)]
    exact (m.etaA a).symm

end GlobalTheory
