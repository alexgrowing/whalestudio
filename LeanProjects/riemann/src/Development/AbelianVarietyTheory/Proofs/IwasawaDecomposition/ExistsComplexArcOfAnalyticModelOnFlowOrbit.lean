import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsComplexArcDatumCmFibre
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProof
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TateIsoExistsLiftOfTwoData

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.CuspFrom

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D D' : Datum H} {k : Type} [Field k]
  {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem tateIso_similar_zeta
    (he : ∀ n x y c c', e n x y c → e n x y c' → c = c') (I : TateIso D k Q act e) (I' : TateIso D' k Q act e) :
    ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ),
      (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → IsCoprime (ν n) (n : ℤ)) ∧
      (∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n) ∧
      (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧
      (∀ n : ℕ, 0 < n → ∀ a, I.ev n a = I'.ev n (f n a)) ∧
      ∀ n : ℕ, 0 < n → I.ζ n = I'.ζ n ^ ν n := by
  have h1 : ∀ n : ℕ, ∃ f : D.La →ₗ[𝓞 E] D'.La, 0 < n → ∀ a, I.ev n a = I'.ev n (f a) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · exact ⟨0, fun h' => absurd h h'.ne'⟩
    · obtain ⟨f, hf⟩ := tateIso_exists_lift_of_two_data I I' h
      exact ⟨f, fun _ => hf⟩
  have h2 : ∀ n : ℕ, ∃ ν : ℕ, 0 < n → I.ζ n = I'.ζ n ^ ν := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | hn
    · exact ⟨1, fun h' => absurd h h'.ne'⟩
    · haveI : NeZero n := ⟨hn.ne'⟩
      obtain ⟨i, -, hi⟩ := (I'.ζ_prim n hn).eq_pow_of_mem_rootsOfUnity
        ((mem_rootsOfUnity _ _).2 (I.ζ_prim n hn).pow_eq_one)
      exact ⟨i, fun _ => hi.symm⟩
  choose f hf using h1
  choose ν hν using h2
  refine ⟨f, fun n => ν n, ?_, ?_, ?_, ?_, ?_, hf, fun n hn => ?_⟩
  · intro n m hn hm a
    rw [← tateIso_ev_eq_iff_add I' hn, ← hf n hn, ← I'.tower n m hn hm, ← hf (n * m) (Nat.mul_pos hn hm),
      I.tower n m hn hm]
  · intro n hn
    refine ⟨fun a => ?_, fun a' => ?_⟩
    · rw [← I'.ker n hn, ← I.ker n hn, hf n hn]
    · obtain ⟨a, ha⟩ := (I.onto n hn _).1 (tateIso_ev_pow I' hn a')
      rw [hf n hn] at ha
      exact ⟨a, (tateIso_ev_eq_iff_add I' hn _ _).1 ha.symm⟩
  · intro n hn
    have h := I.ζ_prim n hn
    rw [hν n hn] at h
    exact Nat.isCoprime_iff_coprime.2 (((I'.ζ_prim n hn).pow_iff_coprime hn _).1 h)
  · intro n m hn hm
    have h : I'.ζ n ^ ν (n * m) = I'.ζ n ^ ν n := by
      rw [← hν n hn, ← I.ζ_pow n m hn hm, hν (n * m) (Nat.mul_pos hn hm), ← I'.ζ_pow n m hn hm, ← pow_mul,
        ← pow_mul, mul_comm m]
    rw [← (I'.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, zpow_natCast, zpow_natCast, h, mul_inv_cancel]
  · intro n hn a b
    have e1 := I'.isom n hn (f n a) (f n b)
    have e2 := I.isom n hn a b
    rw [hf n hn a, hf n hn b] at e2
    have h := he n _ _ _ _ e1 e2
    rw [hν n hn, ← zpow_natCast, ← zpow_mul] at h
    rw [← (I'.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, h, mul_inv_cancel]
  · rw [zpow_natCast]
    exact hν n hn

end

theorem familyUnif_lattice_similar_zeta (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty)
    (i : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (U.Di i) ty P) :
    ∃ (f : ℕ → D.La →ₗ[𝓞 E] (U.Di i).La) (ν : ℕ → ℤ),
      (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ (U.Di i).EF (f n a) (f n a') - ν n * D.EF a a') ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, f l.M a = U.t i a + l.M • e) ∧
      (∀ a, ∃ e, f l.A a = U.t i a + l.A • e) ∧
      σ (baseKA l).ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (ν l.A : ℂ) / l.A) := by
  obtain ⟨-, I, hζ, hA, hM⟩ := Xo.univ.geom ℂ (U.u i P) σ (U.over_σ i P hP)
  obtain ⟨f, ν, h1, h2, -, -, h5, h6, h7⟩ := tateIso_similar_zeta
    (fun n x y c c' => weilIs_unique_fieldPoint _ _ _ Xo.univ.t.PP.isLB ℂ _ n x y c c') I (familyUnifTateIso U hP)
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  refine ⟨f, ν, h1, h2, h5, fun a ha => ?_, fun a => ?_, ?_⟩
  · rw [← tateIso_ev_eq_iff_add (familyUnifTateIso U hP) hM0, ← h6 _ hM0, ← hM a ha]
    exact U.ex_eta i P hP a ha
  · rw [← tateIso_ev_eq_iff_add (familyUnifTateIso U hP) l.A_pos, ← h6 _ l.A_pos, ← hA a]
    exact U.ex_etaA i P hP a
  · rw [← hζ, h7 _ l.A_pos]
    exact expNegUnit_zpow_val _ _

theorem exists_arcIn_input : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (B : GlobalTheory.CM.PAT H (Sp ℂ)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → letI := H.starRing; ∀ (A : AnArc (𝓞 E)) (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] A.La) (ξ : Module.Dual ℤ A.X) (DB : Datum H) (tyB : Fin A.gB → (E →+* ℂ)) (eB : DB.La ≃+ A.abelian₂) (ex : (Fin A.gB → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ B.t.G)), OnOrbit Uw k ξ' x A gam ξ → Module.finrank (𝓞 E) A.X = 1 → (∀ y y', (2 * l.M' : ℤ) ∣ A.be y y') → PrimAn H A → AbDat H A DB tyB eB → DB.p = Dw.p - 1 → DB.q = Dw.q - 1 → 1 ≤ Dw.p → 1 ≤ Dw.q → GlobalTheory.CM.IsExp B (RingHom.id ℂ) DB tyB (A.abelian₂.subtype.toAddMonoidHom.comp eB.toAddMonoidHom) ex → ∃ (aC : ArcIn Dw l (RingHom.id c.F) ℂ σ) (Λ : GtAn₀ aC) (hA : Λ.A = A), (∀ v, Λ.Lifts (aC.eta v) (cast (congrArg AnArc.La hA.symm) (gam (Uw.F.t (Uw.ik k) v)))) ∧ ∀ v, Λ.Lifts (aC.etaA v) (cast (congrArg AnArc.La hA.symm) (gam (Uw.F.t (Uw.ik k) v))) := by
  intro E _ _ _ H Dw l Xo c _ _ σ r U Uw k ξ' x B hσ _
  let _ := H.starRing
  intro A gam ξ DB tyB eB ex ⟨hgam, _, T₀, hT₀⟩ hrk hbe ⟨hχ, hψ⟩ ⟨hF, hty, _, hEF, _⟩ hp hq hp1 hq1
    ⟨_, hol, add, onto, ker, lin, weil⟩
  have hK := GlobalTheory.ArcCM.known_holds
  obtain ⟨T, m, hg⟩ := GlobalTheory.CM.PAT.exists_pullback E H _ _ (spMap (RingHom.id ℂ)) B
  obtain ⟨-, hiso⟩ := GlobalTheory.CM.PAT.exists_of_sabMap E H _ _ _ B _ m
  obtain ⟨w₀, hw₀, -⟩ := m.lin
  obtain ⟨sym, hsym, hsym'⟩ := (GlobalTheory.isSymmetric_iff_exists_gen _ _ T.t.PP).1 T.t.sym
  have := T.t.act.hom H.w0
  obtain ⟨w, hw, hw'⟩ := CxFibre.exists_primGen T.t.PP (T.t.act.act H.w0) T.t.prim
  let oa : T.pol.OAct (𝓞 E) := ⟨T.t.act.toRingAct, fun a =>
    (GlobalTheory.RosLam.rosatiAdj_iff_lamEq hK.laws.globalFns _ T.pol _ _ (T.t.act.hom a) (T.t.act.hom _)).2 (by
      change GlobalTheory.CM.LamEq _ _ _ _ _ (T.t.act.act (H.bar a))
      simpa [GlobalTheory.CM.LamEq] using T.t.adj a)⟩
  obtain ⟨u, χ, hgP, lam, hAH, hrig, hθ, hex⟩ := CxFibre.exists_holUnif_of_exp hK.theta B.t.PP.isLB
    (spMap (RingHom.id ℂ)) T.pol T.t.PP.rig
    T.t.PP.rigGen m.φ m.cart ⟨w₀, hw₀⟩ A.abelian₂ A.discrete A.full A.Hm A.Hm_herm A.Hm_pos (fun a b => A.Ef a b) A.Ef_eq
    ex hol add onto
    (fun z => (ker z).trans ⟨fun ⟨a, ha⟩ => ha ▸ (eB a).2, fun hz => ⟨eB.symm ⟨z, hz⟩, by simp⟩⟩)
    (fun n a b c hn hc => by
      obtain ⟨a, rfl⟩ := eB.surjective a
      obtain ⟨b, rfl⟩ := eB.surjective b
      exact weil n a b c hn (by rw [hEF]; exact hc))
  have hact : ∀ (a : 𝓞 E) z, u.ex (fun i => tyB i (a : E) * z i) = u.ex z ≫ T.t.act.act a := fun a z =>
    Over.OverMorphism.ext (m.cart.1.hom_ext (by
      rw [hex, lin, Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc, hex])
      (by rw [Over.w, Over.w]))
  have hact' : ∀ (a : 𝓞 E) z, u.ex (A.F a z) = u.ex z ≫ T.t.act.act a := fun a z => by
    rw [← hact]; exact congrArg u.ex (funext (hF a z))
  obtain rfl : χ = fun b : u.Λ => A.chi ⟨b, lam.le b.2⟩ := funext fun a => by
    rw [CxFibre.chi_eq T.t.PP.isLB _ w hw u A.Hm χ hAH (A.F H.w0) (hact' _) a
      ⟨_, lam.ge (A.F_mem H.w0 a (lam.le a.2))⟩ rfl, hχ]
    have h₁ := A.Ef_eq_im (A.FLam H.w0 ⟨a, lam.le a.2⟩) ⟨a, lam.le a.2⟩
    rw [← A.H_conj, Complex.conj_im] at h₁
    have h₂ : (hermForm A.Hm a (A.F H.w0 a)).im = -(A.Ef (A.FLam H.w0 ⟨a, lam.le a.2⟩) ⟨a, lam.le a.2⟩ : ℤ) := by
      rw [h₁, neg_neg]; rfl
    generalize A.Ef (A.FLam H.w0 ⟨a, lam.le a.2⟩) ⟨a, lam.le a.2⟩ = n at h₂
    rw [h₂, ← Complex.exp_neg_pi_mul_I, ← Complex.exp_int_mul]
    congr 1
    push_cast
    ring
  obtain ⟨s, hs, -⟩ := hT₀ ((T₀ + 1 : ℝ) * Complex.I) (by simp)
  obtain ⟨f, ν, f₁, f₂, f₃, f₄, f₅, f₆⟩ :=
    familyUnif_lattice_similar_zeta E H Dw l Xo _ _ _ Uw.F (Uw.ik k) _ (Uw.period k ⟨_, hs⟩)
  obtain ⟨a, Λ, hA, -, -, -, -, -, -, heta, hetaA⟩ := GlobalTheory.ArcOfModel.exists_arcIn hK.laws hK.laws2 Dw l
    (RingHom.id c.F) σ T.pol T.t.PP.rig T.t.PP.rigGen T.t.cub sym hsym hsym' oa ⟨w, hw, hw'⟩ A u lam hAH hrig
    (fun j _ => hθ j) hact' hψ (Module.nontrivial_of_finrank_pos (R := 𝓞 E) (hrk ▸ one_pos)) hbe _ gam hgam
    (Uw.F.t (Uw.ik k)) f ν f₁ (fun n hn v => ((f₂ n hn).1 v).1) (fun n hn => (f₂ n hn).2)
    f₃ f₄ f₅
    (fun z hz => (congrArg σ (Subtype.ext hz)).trans f₆)
    (fun ρ hρ τ => by
      obtain ⟨τ₀, rfl⟩ := GlobalTheory.PeriodPoint.exists_embedding (RingHom.id ℂ) τ
      have hρ' : σ ρ = H.rt0 := by
        rw [← hσ]
        exact congrArg σ (Subtype.ext hρ)
      refine ⟨_, CxFibre.lieMult_card hK.theta T.pol hgP u _ tyB hact τ₀, ?_⟩
      rw [hrk, hρ']
      split_ifs with h
      · rw [(hty τ₀).1 h]; omega
      · rw [(hty τ₀).2 h]; omega)
  refine ⟨a, Λ.toGtAn₀, hA, fun v q hq => ?_, fun v q hq => ?_⟩
  · rw [(TorusExt.existsUnique_qkExt a.bimult (algebraMap (FractionRing ℂ) ℂ) (RingHom.comp_id _) _).unique hq (heta v)]
    exact qk_equiv_refl a.bimult _
  · rw [(TorusExt.existsUnique_qkExt a.bimult (algebraMap (FractionRing ℂ) ℂ) (RingHom.comp_id _) _).unique hq (hetaA v)]
    exact qk_equiv_refl a.bimult _

end GlobalTheory.CuspFrom
