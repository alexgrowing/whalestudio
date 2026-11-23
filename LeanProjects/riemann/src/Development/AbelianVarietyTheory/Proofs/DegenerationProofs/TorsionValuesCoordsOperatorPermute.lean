import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.EvCrd
open GlobalTheory.ThetaCompare

theorem defect_eq_one {G U : Type} [CommGroup G] [CommGroup U] (f b n : G → U) (X : G) (N M Q : ℕ) (hN : Odd N)
    (hX : X ^ N = 1) (hM : X ^ M = 1)
    (h₁ : ∀ z, f z ^ Q * (b (X * z) * (b z)⁻¹) = f 1 ^ Q * (b (X * 1) * (b 1)⁻¹))
    (h₂ : ∀ z, b z * (b z⁻¹)⁻¹ * (n z ^ Q)⁻¹ * n (z ^ M) = b 1 * (b 1⁻¹)⁻¹ * (n 1 ^ Q)⁻¹ * n (1 ^ M))
    (hp : ∏ j ∈ Finset.range N, f (X ^ j) = 1) (hs : f X⁻¹ * n 1 * (f 1 * (n X⁻¹)⁻¹) = 1) (z : G) :
    f z ^ Q * (b (X * z) * (b z)⁻¹) = 1 := by
  set κ := f 1 ^ Q * (b (X * 1) * (b 1)⁻¹) with hκ
  have e₁ : κ ^ N = 1 := by
    have : ∀ j ∈ Finset.range N, κ = f (X ^ j) ^ Q * (b (X ^ (j + 1)) / b (X ^ j)) := fun j _ => by
      rw [← h₁ (X ^ j), pow_succ' X j, div_eq_mul_inv]
    rw [show κ ^ N = ∏ _j ∈ Finset.range N, κ by rw [Finset.prod_const, Finset.card_range],
      Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_pow, hp,
      Finset.prod_range_div (fun j => b (X ^ j)) N, hX, pow_zero, div_self', one_pow, _root_.one_mul]
  have e₂ : κ ^ 2 = 1 := by
    have a₁ := h₁ X⁻¹
    have a₂ := h₂ X⁻¹
    have a₃ := congrArg (· ^ Q) hs
    rw [inv_pow, hM, inv_inv, inv_one, one_pow] at a₂
    rw [mul_inv_cancel] at a₁
    rw [_root_.mul_one] at hκ
    simp only [one_pow, mul_pow, inv_pow] at a₃
    rw [sq]
    nth_rewrite 1 [← a₁]
    rw [hκ]
    apply Additive.ofMul.injective
    replace a₂ := congrArg Additive.ofMul a₂
    replace a₃ := congrArg Additive.ofMul a₃
    simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one] at a₂ a₃ ⊢
    linear_combination (norm := module) a₃ - a₂
  obtain ⟨l, rfl⟩ := hN
  rw [pow_succ, pow_mul, e₂, one_pow, _root_.one_mul] at e₁
  exact (h₁ z).trans e₁

variable {S : Scheme.{0}}

open CommPairing GlobalLift in

theorem lift_pow (hG : GlobalFnsSt) (P : PolAV S) {T : Over S} {N M : ℕ} (hN : Odd N)
    {α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ M).left] ![(M : ℤ) ^ 2, -1])}
    (hα : α.IsGen) {x : T ⟶ P.A} (hx : x ^ N = 1) (hM : x ^ M = 1) {θ : ThetaGrp P.A P.L N T}
    (H : SymLift P.A P.L N N x θ) {y : T.left} {J} (hJ : Good P.L y J) (z : T ⟶ P.A) :
    tval θ (ptSecT P.A z).left y J ^ (M ^ 2) *
        (val α (ptSecT P.A (x * z)).left y J ^ N * (val α (ptSecT P.A z).left y J ^ N)⁻¹) = 1 := by
  have := P.isAb.comm
  obtain ⟨rfl, hp, ν, hν, hs⟩ := H
  have rα := Reg.two (y := y) (J := J) α hα (snd T P.A) (snd T P.A ^ M) rfl rfl
  have rb := rα.pow hJ N
  have rf := Reg.two (y := y) (J := J) (φ := ![(snd T P.A).left, (translPt P.A θ.pt).left]) θ.φ θ.isGen
    (snd T P.A) (translPt P.A θ.pt) rfl rfl
  have rn := Reg.two (y := y) (J := J) (φ := ![(snd T P.A).left, (snd T P.A ≫ (GrpObj.inv : P.A ⟶ P.A)).left]) ν hν
    (snd T P.A) (snd T P.A)⁻¹ rfl rfl
  have c₁ := ((rf.pow hJ (M ^ 2)).mul hJ ((rb.pull hJ (translPt P.A θ.pt)).mul hJ rb.inv)).const hG P.isAb P.isLB hJ
    (fun U _ h => by
      have q : translPt P.A θ.pt ^ M = snd T P.A ^ M := by
        rw [show translPt P.A θ.pt = (fst T P.A ≫ θ.pt) * snd T P.A from rfl, mul_pow, ← SymLiftOdd.comp_pow', hM,
          MonObj.comp_one, _root_.one_mul]
      simp only [SymLiftOdd.comp_pow', lift_snd, q]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_zpow, ofMul_one]
      module)
  have c₂ := (((rb.mul hJ (rb.pull hJ (snd T P.A)⁻¹).inv).mul hJ (rn.pow hJ (M ^ 2)).inv).mul hJ
    (rn.pull hJ (snd T P.A ^ M))).const hG P.isAb P.isLB hJ (fun U _ h => by
      simp only [SymLiftOdd.comp_pow', SymLiftOdd.comp_inv', lift_snd, inv_pow]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_zpow, ofMul_one]
      module)
  simp only [pt_translPt, SymLiftOdd.comp_pow', SymLiftOdd.comp_inv', pt_snd] at c₁ c₂
  have q₁ := val_corr hJ hp (ptSecT P.A 1).left
  have q₂ := val_corr hJ hs (ptSecT P.A 1).left
  rw [GlobalLift.val_powGen _ _ _ hJ, val_one] at q₁
  rw [GlobalLift.val_symGen _ _ _ hJ, val_one, pt_translT, pt_negT, _root_.mul_one, inv_one] at q₂
  simp only [pt_translT, _root_.mul_one] at q₁
  exact defect_eq_one (fun z => tval θ (ptSecT P.A z).left y J)
    (fun z => val α (ptSecT P.A z).left y J ^ N)
    (fun z => nval ν (ptSecT P.A z).left y J) θ.pt N M (M ^ 2) hN hx hM
    (fun z => c₁ z 1) (fun z => c₂ z 1) ((Finset.prod_range _).trans q₁) q₂ z

theorem sval_sum {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} {a : ℤ} {I : Type} [Fintype I]
    {s : I → LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T)} {c : I → Γ(T.left, ⊤)}
    (H : ∀ j, s'.f j = ∑ l, liftFun A _ (c l) * (s l).f j) (x : T ⟶ A) {z : T.left} {J} (hJ : Good L z J) :
    sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' (ptSecT A x).left z J =
      ∑ l, gs (𝟙 _) z ⊤ (c l) *
        sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) (s l) (ptSecT A x).left z J := by
  have hy := hJ.mem (fun _ : Fin 1 => (snd T A).left) (ptSecT A x).left
  refine (congrArg (gs _ z _) (H _)).trans ?_
  have hs : ∀ (W : (T ⊗ A).left.Opens) (_ : (ptSecT A x).left z ∈ W) (u : I → Γ((T ⊗ A).left, W)),
      gs (ptSecT A x).left z W (∑ l, u l) = ∑ l, gs (ptSecT A x).left z W (u l) := fun W hW u => by
    simp only [gs_eq _ z W hW, map_sum]
  refine (hs _ hy _).trans (Finset.sum_congr rfl fun l _ => (gs_mul _ z _ hy _ _).trans (congrArg (· * _) ?_))
  refine (gs_res _ z _ hy _).trans ((gs_pull _ (fst T A).left z ⊤ trivial _).trans ?_)
  rw [← Over.comp_left, ptSecT, lift_fst]; rfl

open CommPairing in

theorem exists_root_stalk (hG : GlobalFnsSt) (P : PolAV S) {T : Over S} {N M : ℕ} (hN : Odd N)
    {rig : LB.Gen (P.L.pull (eSec P.A))} {x h w : T ⟶ P.A} (hx : x ^ N = 1) (hM : x ^ M = 1) (hw : w = x * h)
    {θ : ThetaGrp P.A P.L N T} (H : SymLift P.A P.L N N x θ) {τ τ'} (hτ : IsTorsFrame P rig M h τ)
    (hτ' : IsTorsFrame P rig M w τ') (y : T.left) :
    ∃ ξ : (T.left.presheaf.stalk y)ˣ, ξ ^ (M ^ 2) = 1 ∧
      ∀ (I : Type) [Fintype I] (s : I → LB.Sec (LPow P.A P.L N T)) (t : LB.Sec (LPow P.A P.L N T))
        (c v : I → Γ(T.left, ⊤)) (v' : Γ(T.left, ⊤)),
        (∀ σ, IsActOf P.A P.L N θ t σ → ∀ j, σ.f j = ∑ l, liftFun P.A _ (c l) * (s l).f j) →
        (∀ l, IsValueAt P.A P.L N (s l) h (powFrame P.A P.L h τ N) (v l)) →
        IsValueAt P.A P.L N t w (powFrame P.A P.L w τ' N) v' →
        ∑ l, gs (𝟙 _) y ⊤ (c l) * gs (𝟙 _) y ⊤ (v l) = ξ.val * gs (𝟙 _) y ⊤ v' := by
  subst hw
  choose J hJ using fun χ : T.left ⟶ P.A.left => exists_chart P.isLB (χ y)
  replace hJ : Good P.L y J := hJ
  obtain ⟨β, hβ, -⟩ := hτ.2.2
  obtain ⟨α, hα, -⟩ := VVRank.exists_gen_pullTo (φ' := ![(snd T P.A).left, (snd T P.A ^ M).left]) β hβ
    (snd T P.A).left (fun k => by
      fin_cases k
      · exact Category.comp_id _
      · change (snd T P.A).left ≫ (mulA P.A M).left = (snd T P.A ^ M).left
        rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id])
  have a₁ := lift_pow hG P hN hα hx hM H hJ h
  have a₂ := torsFrame_pow hG P hα hτ hJ
  have a₃ := torsFrame_pow hG P hα hτ' hJ
  refine ⟨tval θ (ptSecT P.A h).left y J * val τ' (𝟙 _) y J ^ N * (val τ (𝟙 _) y J ^ N)⁻¹, ?_,
    fun I _ s t c v v' hc hv hv' => ?_⟩
  · apply Additive.ofMul.injective
    replace a₁ := congrArg Additive.ofMul a₁
    replace a₂ := congrArg Additive.ofMul a₂
    replace a₃ := congrArg Additive.ofMul a₃
    simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one] at a₁ a₂ a₃ ⊢
    linear_combination (norm := module) a₁ + N • a₃ - N • a₂
  · obtain ⟨σ, hσ⟩ : ∃ σ, IsActOf P.A P.L (N : ℤ) θ t σ := VVRank.exists_isTwistPull P.A P.isLB θ.isGen t
    have p : ∀ (z : T ⟶ P.A) (e), val (powFrame P.A P.L z e N) (𝟙 _) y J = val e (𝟙 _) y J ^ N := fun z e =>
      (map_zpow _ _ _).trans (zpow_natCast _ _)
    have b₁ := sval_twist hσ (ptSecT P.A h).left hJ
    have b₂ := sval_sum (hc σ hσ) h hJ
    have b₃ := sval_valueAt hv' hJ
    rw [pt_translT, congrArg (fun q => ptSecT P.A (q * h)) H.pt_eq, b₃, b₂, p] at b₁
    simp only [fun l => sval_valueAt (hv l) hJ, p, ← _root_.mul_assoc, ← Finset.sum_mul] at b₁
    rw [(Units.eq_mul_inv_iff_mul_eq _).2 b₁, Units.val_mul, Units.val_mul]
    change (tval θ (ptSecT P.A h).left y J).val * _ * _ * _ = _
    ring

theorem valR_comp {R : Type} [CommRing R] {X Y : Scheme.{0}} (x : Sp R ⟶ Y) (g : Y ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ g ⁻¹ᵁ U) (f : Γ(X, U)) : valR x (g ⁻¹ᵁ U) ((g.app U).hom f) = valR (x ≫ g) U f := by
  rw [CrdCalc.valR_eq x _ h, CrdCalc.valR_eq (x ≫ g) U h]
  rfl

theorem valR_fn {R K : Type} [CommRing R] [CommRing K] (y : R →+* K) (b : R) : valR (spMap y) ⊤ (fn b) = y b := by
  rw [CrdCalc.valR_eq _ _ le_rfl]
  have n := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom y)
  have e := congrArg (fun q => q.hom b) n
  change (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (y b) = (spMap y).appTop.hom (fn b) at e
  have e' : ((spMap y).appLE ⊤ ⊤ le_rfl) = (spMap y).appTop := (Scheme.Hom.app_eq_appLE _).symm
  change (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (((spMap y).appLE ⊤ ⊤ le_rfl).hom (fn b)) = _
  rw [e', ← e]
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).inv_hom_id_apply _

theorem crd_of_isValueAt {R K : Type} [CommRing R] [Field K] (y : R →+* K) (P : PolAV (Sp R)) {k : ℤ} {I : Type}
    {s : I → LB.Sec (LPow P.A P.L k (baseOver (Sp R)))} {z : baseOver (Sp R) ⟶ P.A} {τ} {v : I → R}
    (H : ∀ i, IsValueAt P.A P.L k (s i) z τ (fn (v i))) :
    Crd (LPow P.A P.L k (baseOver (Sp R))) s (spMap y ≫ (ptSecT P.A z).left) (fun i => y (v i)) := by
  let x : Sp K ⟶ (baseOver (Sp R)).left := spMap y
  obtain ⟨j₀, hj⟩ := exists_chart P.isLB (z.left (x (IsLocalRing.closedPoint K)))
  let W := LB.wchart P.L (fun _ : Fin 1 => z.left) (fun _ => j₀)
  have hW : ⊤ ≤ x ⁻¹ᵁ W := (CrdCalc.top_le_iff x W).2 (Set.mem_iInter.2 fun _ => hj)
  have hU := hW.trans (x.preimage_mono (val_le P.A P.L z (fun _ => j₀)))
  refine ⟨fun _ => j₀, (Units.map (CrdCalc.valHom x W hW).toMonoidHom (τ.s fun _ => j₀))⁻¹, hU, fun i => ?_⟩
  have e := congrArg (valR x W) (H i fun _ => j₀)
  have e₁ := ((CrdCalc.valR_res x (val_le P.A P.L z (fun _ => j₀)) hW _).trans
    (valR_comp x (ptSecT P.A z).left _ hU ((s i).f fun _ => j₀))).symm.trans e
  have e₂ := e₁.trans ((CrdCalc.valR_mul x W hW _ _).trans (congrArg₂ (· * ·)
    ((CrdCalc.valR_res x le_top hW _).trans (valR_fn y (v i))) (CrdCalc.valR_eq x W hW _)))
  refine (Units.eq_inv_mul_iff_mul_eq _).2 ?_
  exact (mul_comm _ _).trans e₂.symm

theorem ev_crd_act : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), (∀ (K : Type) [Field K] (y : S.R →+* K) (a : S.Gam), ρ.Crd (spMap y ≫ (ρ.pt a).left) (fun i => y ⟨S.ev a i, S.ev_mem a i⟩)) ∧ ∀ a h : S.Gam, ∃ e : ℕ, ∀ i, ∑ n, algebraMap o Ω (S.ρ a n i) * S.ev h n = algebraMap o Ω (S.ζ ^ e) * S.ev (h + S.r • a) i := by
  intro hL o Ω _ _ _ hb S ρ
  refine ⟨fun K _ y a => ⟨_, ?_, crd_of_isValueAt y ρ.P (fun i => ρ.ev_val i a)⟩, fun a h => ?_⟩
  · rw [Category.assoc, ← Over.comp_left, pt_snd]
  have := ρ.P.isAb.comm
  have hN : Odd S.N := by rw [ρ.N_eq]; exact ρ.n_odd.pow.pow
  have h₀ : ρ.pt 0 = 1 := by
    have := ρ.pt_add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hp : ∀ (n : ℕ) b, ρ.pt (n • b) = ρ.pt b ^ n := fun n b => by
    induction n with
    | zero => rw [zero_smul, h₀, pow_zero]
    | succ n ih => rw [succ_nsmul, ρ.pt_add, ih, pow_succ]
  have hx : ρ.pt (S.r • a) ^ S.N = 1 := by rw [hp, ← pow_mul, (ρ.fr_tors a).1]
  let iso := Scheme.ΓSpecIso (CommRingCat.of S.R)
  let y : Sp S.R := (⊥ : PrimeSpectrum S.R)
  obtain ⟨ξ, hξ, e⟩ := exists_root_stalk hL.1.globalFns ρ.P hN hx (ρ.fr_tors _).1
    (by rw [ρ.pt_add, mul_comm]) (ρ.U_sym a) (ρ.fr_tors h) (ρ.fr_tors (h + S.r • a)) y
  let g : S.R →+* (Sp S.R).presheaf.stalk y := ((Sp S.R).presheaf.germ ⊤ y trivial).hom.comp iso.inv.hom
  have hg : Function.Injective g :=
    (germ_injective_of_isIntegral (Sp S.R) (U := ⊤) y trivial).comp (ConcreteCategory.bijective_of_isIso iso.inv).1
  have hgs : ∀ b : S.R, gs (𝟙 (baseOver (Sp S.R)).left) y ⊤ (fn b) = g b := fun b => gs_eq _ y ⊤ trivial _
  have hi : Function.Injective (algebraMap o S.R) := fun b b' h => hb.inj (congrArg Subtype.val h)
  have hζ : IsPrimitiveRoot (g (algebraMap o S.R S.ζ)) ((S.r * S.N) ^ 2) :=
    (S.prim.map_of_injective hi).map_of_injective hg
  have : NeZero ((S.r * S.N) ^ 2) := ⟨(pow_pos (Nat.mul_pos S.r_pos hN.pos) 2).ne'⟩
  have : IsDomain ((baseOver (Sp S.R)).left.presheaf.stalk y) := inferInstanceAs (IsDomain ((Sp S.R).presheaf.stalk y))
  obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one (ξ := ξ.val) (congrArg Units.val hξ)
  refine ⟨k, fun i => ?_⟩
  have e' := e S.J ρ.s (ρ.s i) _ _ _ (ρ.U_act a i) (fun l => ρ.ev_val l h) (ρ.ev_val i _)
  simp only [hgs] at e'
  have q : ∑ n, algebraMap o S.R (S.ρ a n i) * ⟨S.ev h n, S.ev_mem _ _⟩ =
      algebraMap o S.R (S.ζ ^ k) * ⟨S.ev (h + S.r • a) i, S.ev_mem _ _⟩ := hg (by
    rw [map_sum, map_mul, map_pow, map_pow, hk]
    simp only [map_mul]
    exact e')
  have q' := congrArg S.R.val q
  rw [map_sum] at q'
  exact q'

end GlobalTheory.ZH.EvCrd
end
