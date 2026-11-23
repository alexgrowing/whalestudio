import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Taylor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.L2NormFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueExistsUniqueOfChartIndependence
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTranslationSectionsUniversalObject
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesTestFunctionHolomorphicWeight
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisenbergOperatorRationalPointLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockHxDifferentiable
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HarmonicConnectionValueEqPolynomialDerivativeStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SectionsReadAsTranslatesAtScaledPointStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ThVal

open scoped ContDiff

section Deriv

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

open ReciprocityTheory.ChartRestriction.G.PullbackSections (mD mD_coe lD_eq) in

theorem polyDeriv_eq_mD {θ : V → ℂ} {x : V} (hθ : ContDiffAt ℂ ω θ x) {T₁ : Type} (P : MvPolynomial T₁ ℂ)
    (u : T₁ → V) :
    I2.polyDeriv P u θ x = ∑ m ∈ P.support, P.coeff m * mD θ x ((Finsupp.toMultiset m).map u) := by
  unfold I2.polyDeriv
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  have hL : (((Finsupp.toMultiset m).toList.map u : List V) : Multiset V) =
      (Finsupp.toMultiset m).map u := by
    rw [← Multiset.map_coe, Multiset.coe_toList]
  rw [← hL, mD_coe hθ, lD_eq θ x _ (n := Multiset.card (Finsupp.toMultiset m))
    (by rw [List.length_map, Multiset.length_toList])]
  congr 1
  funext k
  simp [List.get_eq_getElem]

theorem polyDeriv_rename {θ : V → ℂ} {x : V} (hθ : ContDiffAt ℂ ω θ x) {T₁ κ : Type} (ρ : T₁ → κ)
    (hρ : Function.Injective ρ) (P : MvPolynomial T₁ ℂ) (v : κ → V) :
    I2.polyDeriv (MvPolynomial.rename ρ P) v θ x = I2.polyDeriv P (v ∘ ρ) θ x := by
  rw [polyDeriv_eq_mD hθ, polyDeriv_eq_mD hθ, MvPolynomial.support_rename_of_injective hρ,
    Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective hρ h)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_rename_mapDomain ρ hρ, ← Finsupp.toMultiset_map, Multiset.map_map]

theorem polyDeriv_scale {T₁ : Type} (Q : MvPolynomial T₁ ℂ) (u : T₁ → V) (G : V → ℂ) (t : ℂ) (ht : t ≠ 0) (d : ℕ)
    (hd : ∀ m ∈ Q.support, Multiset.card (Finsupp.toMultiset m) = d) :
    I2.polyDeriv Q u (fun z => G (t • z)) 0 = t ^ d * I2.polyDeriv Q u G 0 := by
  unfold I2.polyDeriv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  let g : V ≃L[ℂ] V := ContinuousLinearEquiv.smulLeft (R₁ := ℂ) (Units.mk0 t ht)
  have hg : ∀ z, g z = t • z := fun _ => rfl
  have h := ContinuousLinearEquiv.iteratedFDerivWithin_comp_right g G (s := Set.univ) uniqueDiffOn_univ
    (x := 0) (Set.mem_univ _) (Multiset.card (Finsupp.toMultiset m))
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ, map_zero] at h
  have e : (fun z => G (t • z)) = G ∘ g := rfl
  rw [e, h, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [ContinuousLinearEquiv.coe_coe, hg]
  rw [ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← hd m hm, smul_eq_mul]
  ring

end Deriv

theorem card_eq_totalDegree {T k : Type} [Fintype T] [Field k] {r : T → ℕ} {n : ℕ} {a : T → ℕ → ℕ}
    {P : MvPolynomial (Letter T r n) k} (hP : RowDeg r n k a P) :
    ∀ m ∈ P.support, Multiset.card (Finsupp.toMultiset m) = P.totalDegree := by
  have h : ∀ m ∈ P.support, (m.sum fun _ e => e) = ∑ σ : T, ∑ i : Fin (r σ), a σ i := by
    intro m hm
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => hP m hm σ i
  intro m hm
  rw [Finsupp.card_toMultiset]
  refine le_antisymm (MvPolynomial.le_totalDegree hm) (Finset.sup_le fun m' hm' => ?_)
  exact ((h m' hm').trans (h m hm).symm).le

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {r : ℕ}

theorem smul_mem_of_rep (l : Geo.Tor.Level H) (L : Lt E r) (mk : Dw.La →ₗ[𝓞 E] (Fin r → E))
    (hm : ∀ a, mk a ∈ L) (Y : Fin r → E) (a : Dw.La) (ha : a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La))
    (hY : Y - ((l.M : E)⁻¹) • mk a ∈ L) (t : 𝓞 E) (ht : t ∈ l.Mb) : t • Y ∈ L := by
  have hM : (l.M : E) ≠ 0 := Nat.cast_ne_zero.2 (by have := l.three_le; omega)
  have h1 : t • a ∈ (l.Mb * Mfr l) • (⊤ : Submodule (𝓞 E) Dw.La) := by
    rw [mul_smul]
    exact Submodule.smul_mem_smul ht ha
  rw [show l.Mb * Mfr l = Ideal.span {(l.M : 𝓞 E)} from l.prod, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨b, -, hb⟩ := h1
  have h2 : t • ((l.M : E)⁻¹ • mk a) = mk b := by
    rw [smul_comm, ← map_smul, ← hb, Nat.cast_smul_eq_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul E,
      smul_smul, inv_mul_cancel₀ hM, one_smul]
  have h3 : t • Y = t • (Y - ((l.M : E)⁻¹) • mk a) + mk b := by rw [smul_sub, h2, sub_add_cancel]
  rw [h3]
  exact L.add_mem (L.smul_mem t hY) (hm b)

theorem level_mem (l : Geo.Tor.Level H) : (l.M : 𝓞 E) ∈ l.Mb :=
  by
  have h := Ideal.mem_span_singleton_self (l.M : 𝓞 E)
  rw [← l.prod] at h
  exact Ideal.mul_le_left h

theorem root_laws (l : Geo.Tor.Level H) (L : Lt E r) (Y : Fin r → E) (h1 : ∀ t ∈ l.Mb, t • Y ∈ L) (j : ℕ)
    (hj : ∀ s ∈ l.Mb ^ j, ∃ u ∈ L, s • Y = (2 * l.M) • u) :
    (∀ s ∈ l.Mb ^ 2, s • ((l.M : E)⁻¹ • Y) ∈ L) ∧
      ∃ u ∈ L, (l.M ^ 2 : ℕ) • ((l.M : E)⁻¹ • Y) = (2 : ℕ) • u := by
  have hM : (l.M : E) ≠ 0 := Nat.cast_ne_zero.2 (by have := l.three_le; omega)
  have key : ∀ (N N' : ℕ), (N : E) ≠ 0 → N * N' = 2 * l.M → ∀ I : Ideal (𝓞 E), l.Mb ⊔ I = ⊤ →
      ∀ K : Ideal (𝓞 E), K * I ≤ l.Mb * Ideal.span {(N : 𝓞 E)} → ∀ s ∈ K, s • ((N : E)⁻¹ • Y) ∈ L := by
    intro N N' hN hNN I hI K hK
    let J : Ideal (𝓞 E) := L.comap (LinearMap.toSpanSingleton (𝓞 E) _ ((N : E)⁻¹ • Y))
    have hJ1 : l.Mb ^ j ≤ J := by
      intro s hs
      obtain ⟨u, hu, e⟩ := hj s hs
      show s • ((N : E)⁻¹ • Y) ∈ L
      rw [smul_comm, e, ← hNN, mul_smul, ← Nat.cast_smul_eq_nsmul E N, smul_smul, inv_mul_cancel₀ hN, one_smul]
      exact nsmul_mem hu _
    have hJ2 : l.Mb * Ideal.span {(N : 𝓞 E)} ≤ J := by
      refine Ideal.mul_le.2 fun s hs t ht => ?_
      obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 ht
      show (s * (w * (N : 𝓞 E))) • ((N : E)⁻¹ • Y) ∈ L
      rw [← _root_.mul_assoc, mul_smul, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E N, smul_smul,
        mul_inv_cancel₀ hN, one_smul]
      exact h1 _ (l.Mb.mul_mem_right w hs)
    have hc : l.Mb ^ j ⊔ I = ⊤ := Ideal.pow_sup_eq_top hI
    have : K ≤ J := by
      calc K = K * (l.Mb ^ j ⊔ I) := by rw [hc, Ideal.mul_top]
        _ = K * l.Mb ^ j ⊔ K * I := Ideal.mul_sup _ _ _
        _ ≤ J := sup_le (Ideal.mul_le_right.trans hJ1) (hK.trans hJ2)
    exact fun s hs => this hs
  refine ⟨key l.M 2 hM (mul_comm _ _) _ l.coprime _ (by rw [← l.prod, pow_two, _root_.mul_assoc]), ?_⟩
  have h2 : l.Mb ⊔ Ideal.span {((2 : ℕ) : 𝓞 E)} = ⊤ := by
    obtain ⟨k, hk⟩ := l.odd
    rw [Ideal.eq_top_iff_one]
    have e : (1 : 𝓞 E) = (l.M : 𝓞 E) + (-(k : 𝓞 E)) * ((2 : ℕ) : 𝓞 E) := by rw [hk]; push_cast; ring
    rw [e]
    exact Submodule.add_mem_sup (level_mem l) (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
  have h3 := key 2 l.M (by norm_num) rfl _ h2 l.Mb le_rfl _ (level_mem l)
  refine ⟨_, h3, ?_⟩
  rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E,
    smul_smul, smul_smul, smul_smul]
  congr 1
  push_cast
  field_simp

section Points

variable {g : ℕ} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r}
  {L : Lt E r} {y : FrPt Xo c ℂ}

theorem pv_add (u v : Fin r → E) : pv X idx x (u + v) = pv X idx x u + pv X idx x v := by
  funext j
  simp [pv, per_add]

theorem ex_pv_mem (A : AnFib X bas idx e x L y) {v : Fin r → E} (hv : v ∈ L) : A.ex (pv X idx x v) = 1 :=
  (A.ex_ker _).2 ⟨v, hv, rfl⟩

theorem ex_pv_pow (A : AnFib X bas idx e x L y) (v : Fin r → E) (k : ℕ) :
    A.ex (pv X idx x v) ^ k = A.ex (pv X idx x (k • v)) := by
  induction k with
  | zero => rw [pow_zero, zero_smul, ex_pv_mem A L.zero_mem]
  | succ k ih => rw [pow_succ, ih, succ_nsmul, pv_add, A.ex_add]

theorem ex_pv_act (A : AnFib X bas idx e x L y) (v : Fin r → E) (s : 𝓞 E) :
    A.ex (pv X idx x v) ≫ Xo.univ.t.act.act s = A.ex (pv X idx x (s • v)) := by
  rw [← A.ex_lin]
  congr 1
  funext j
  exact (per_smul X x (s : E) v (idx j)).symm

theorem levPt_congr {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X) {a b : Dw.La}
    (h : a - b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) : levPt Xo x0 a = levPt Xo x0 b := by
  have : Xo.univ.eta a = Xo.univ.eta b := by
    rw [← sub_add_cancel a b, Xo.univ.eta_add, Xo.univ.eta_ker _ h, _root_.one_mul]
  rw [levPt, levPt, this]

end Points

end GlobalTheory.Dict.ThVal

namespace GlobalTheory.Dict

open ThVal in

theorem thVal_eq_thP : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (q0 n : ℕ) (hr : X.p0 + q0 = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)), r = Dw.p + Dw.q → Even n → (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) → ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (θ : (Fin g → ℂ) → ℂ) (v : TF n g) (κ : ℂ), A.Reads 1 y.s θ → IsVac X bas (H.w0 : E) (tens (stdL E n) L) v → (∀ z : Fin n → Fin g → ℂ, ∏ b, θ (z b) = κ * thA X bas idx v x z) → ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk → A.Marked mk → ∀ (xs : Fin n → Dw.La) (Y : Matrix (Fin n) (Fin r) E), (∀ b, (∃ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), a - xs b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ∧ Y b - ((l.M : E)⁻¹) • mk a ∈ L) ∧ ∃ j : ℕ, ∀ s ∈ l.Mb ^ j, ∃ u ∈ L, s • Y b = (2 * l.M) • u) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ v0 : ℂ, ThValAt Xo c nab y xs P v0 → v0 = κ * thP X hr bas idx (heisG X bas Y v) (MvPolynomial.rename eL (MvPolynomial.map (algebraMap c.F ℂ) P)) x := by
  intro hci E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A hs hx hL q0 n hr eL _ hn hdir _ nab hnab θ v κ hθ hv hκ
    mk hmk hA xs Y hY a P hP v0 hv0
  have hlaws : Laws := GlobalTheory.firstFiveLaws.1
  have hM : (l.M : E) ≠ 0 := Nat.cast_ne_zero.2 (by have := l.three_le; omega)
  have hMc : (l.M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by have := l.three_le; omega)
  have hMY : ∀ b, (l.M : E) • ((l.M : E)⁻¹ • Y b) = Y b := fun b => by
    rw [smul_smul, mul_inv_cancel₀ hM, one_smul]
  have hroot : ∀ b, (∀ s ∈ l.Mb ^ 2, s • ((l.M : E)⁻¹ • Y b) ∈ L) ∧
      ∃ u ∈ L, (l.M ^ 2 : ℕ) • ((l.M : E)⁻¹ • Y b) = (2 : ℕ) • u := fun b => by
    obtain ⟨⟨a', ha', -, hYa⟩, j, hj⟩ := hY b
    exact root_laws l L (Y b) (smul_mem_of_rep l L mk hmk.mem (Y b) a' ha' hYa) j hj
  have hpow : ∀ b, A.ex (pv X idx x ((l.M : E)⁻¹ • Y b)) ^ l.M = levPt Xo y.x (xs b) := fun b => by
    obtain ⟨⟨a', ha', hax, hYa⟩, -⟩ := hY b
    rw [ex_pv_pow, ← Nat.cast_smul_eq_nsmul E, hMY, ← levPt_congr y.x hax, hA a' ha',
      ← sub_add_cancel (Y b) ((l.M : E)⁻¹ • mk a'), pv_add, A.ex_add, ex_pv_mem A hYa, _root_.one_mul]
  have hF : ∀ b, ∃ F, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M
      (fun t' => t' = A.ex (pv X idx x ((l.M : E)⁻¹ • Y b))) y.s (levPt Xo y.x (xs b)) F := fun b => by
    refine (GlobalTheory.exists_isVtOver_and_existsUnique_isUUOver hlaws E H Dw l Xo l.M l.odd _ y.s).1 _ _ _
      (hpow b) ?_ rfl
    obtain ⟨u, hu, hu'⟩ := (hroot b).2
    rw [ex_pv_pow, hu']
    exact ex_pv_mem A (nsmul_mem hu 2)
  choose F hF using hF
  have hval : ThValAt Xo c nab y xs P (thExpr Xo c nab y P F) := by
    refine ⟨ℂ, inferInstance, inferInstance, AlgHom.id _ _, y, F, RingHom.FaithfullyFlat.of_bijective Function.bijective_id,
      GlobalTheory.FramedBaseChange.refl y, fun b => ?_, rfl⟩
    obtain ⟨t', α₀, α, s₁, U, h1, h2, h3⟩ := hF b
    refine ⟨t', α₀, α, s₁, U, h1, fun s hs => ?_, h3⟩
    rw [h2, ex_pv_act]
    exact ex_pv_mem A ((hroot b).1 s hs)
  have huniq := (GlobalTheory.thValTot_of_chartIndep hlaws hci E H Dw l Xo c nab hnab ℂ y a n xs P hP).unique hv0 hval
  have hread : ∀ b, A.Reads ((l.M : ℤ) ^ 2) (F b)
      (fun z => fock X bas idx x 1 (pv X idx x (Y b)) θ ((l.M : ℂ) • z)) := fun b => by
    have := (GlobalTheory.T.sections_read_as_translates_at_scaled_point E H Dw l Xo c r g X bas idx e x L y A hs hx hL l.M l.odd θ hθ).2 _ (hroot b).2 _ _ (hF b)
    rwa [hMY] at this
  have hnv := GlobalTheory.T.harmonicConnectionValue_eq_polynomial_derivative hci E H Dw l Xo c r g X bas idx e x L y A hs hx hL nab hnab n l.M a P hP.1 F _ hread
  have hfock := (GlobalTheory.Dict.fock_laws E r X g bas idx n hs hn x hx 1 θ).2.2.2.2 (fun _ => θ) κ v hv.1 hκ Y
  have hsb : IsSB (heisG X bas Y v) := (GlobalTheory.SW.heisS_laws _ _ _ _ v hv.1).1
  have han := (GlobalTheory.SW.theta_holomorphic_weight E r X g q0 hr bas idx n hs hn (fun _ _ => 0) (fun _ _ => 0) _ hsb 0
    (zero_mem _)).2.2.2 x hx
  have hcd := han.contDiff (n := ⊤)
  have hfun : (fun z : Fin n → Fin g → ℂ => ∏ b, fock X bas idx x 1 (pv X idx x (Y b)) θ ((l.M : ℂ) • z b)) =
      fun z => (κ • thA X bas idx (heisG X bas Y v) x) ((l.M : ℂ) • z) := funext fun z => hfock ((l.M : ℂ) • z)
  have hdeg : ∀ m ∈ (MvPolynomial.map (algebraMap c.F ℂ) P).support,
      Multiset.card (Finsupp.toMultiset m) = P.totalDegree := fun m hm =>
    card_eq_totalDegree hP.1.2.2 m (MvPolynomial.support_map_subset _ _ hm)
  rw [huniq, thExpr, hnv, hfun, polyDeriv_scale _ _ _ _ hMc _ hdeg,
    I2.polyDeriv_smul_fun _ _ (hcd.of_le le_top), thP, polyDeriv_rename hcd.contDiffAt _ eL.injective,
    show letterDir X hr idx ∘ eL = _ from funext hdir, map_inv₀, map_pow, map_natCast, ← _root_.mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero _ hMc), _root_.one_mul]

end GlobalTheory.Dict
