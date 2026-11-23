import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.VdHLeNatAbs
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortGeneratorPlaceValuationBoundProof

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.SupFull

section Coprime
open GlobalTheory.ShortPrime
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem ell_part (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (hst : ∀ a : 𝓞 E, star a = H.bar a) (T : CDVR)
    (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (hC : Good3 C) (nab : NabV Xo c)
    (hnab : IsNab Xo c nab) (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (he : 0 < e) (hB : ChBound C e ρ w n)
    (ℓ : ℕ) (hp : ℓ.Prime) (hl : ¬ IsUnit (ℓ : T.V)) (Λ : GenLat E n) (N M : ℕ) (hU : Λ.Unimod) (hL : Λ.LevOK N M)
    (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmL c Λ w)
    (hR : AllRat Xo (xOf y) (N ^ 2)) (J : Type) [Fintype J] (a : J → Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G))
    (hinj : Function.Injective a) (ha : ∀ u, (∃ i, a i = u) ↔ (InZh Xo Λ N u ∧ ∀ b, ∃ j : ℕ, u b ^ (ℓ ^ j) = 1))
    (F₀ : Fin n → SecN Xo (xOf y) (N ^ 2)) (F : J → Fin n → SecN Xo (xOf y) (N ^ 2))
    (hre : ∀ b, Reach Xo (sOf1 y) (N ^ 2) (F₀ b))
    (hfix : ∀ b (u : ptO Xo (xOf y) ⟶ Xo.univ.t.G), (∃ j : ℕ, u ^ (ℓ ^ j) = 1) → u ^ N = 1 → Moves Xo u (F₀ b) (F₀ b))
    (hF : ∀ i b, Moves Xo (a i b) (F₀ b) (F i b)) :
    letI := io.toAlgebra
    ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) *
      ∑ i, hv Xo c nab y.1 (N ^ 2) (F i) P) := by
  letI := io.toAlgebra
  obtain ⟨A, hsim⟩ := GlobalTheory.T.exists_adapted_similitude_data_at_prime E H n Λ N M ℓ hU hL hp
  have hN : Odd N := hL.1
  have hkN : Odd (A.k * N) := A.odd.mul hN
  have hlev : (A.k * N) ^ 2 = N ^ 2 * A.k ^ 2 := by ring
  have hz := fun u hu => GlobalTheory.inZh_iff_kills_adapted E H Dw l Xo n Λ N ℓ hp hN.pos A (ptO Xo (xOf y)) u hu
  have ha' : ∀ u, (∃ i, a i = u) ↔ (Kills Xo (A.p * A.q) u ∧ ∀ b, ∃ j : ℕ, u b ^ (ℓ ^ j) = 1) := fun u =>
    (ha u).trans (and_congr_left fun hu => (hz u hu).1)
  have hZ : ∀ i, InZh Xo Λ (A.k * N) (a i) := fun i =>
    have h := (ha' _).1 ⟨i, rfl⟩
    (hz _ h.2).2.2 h.1
  obtain ⟨π, hπ⟩ := exists_perm Xo A.cop _ a hinj ha'
  have hpull := fun G => (GlobalTheory.existsUnique_pulls E H Dw l Xo _ (xOf y) (A.k : 𝓞 E) (A.k ^ 2) (N ^ 2) ((A.k * N) ^ 2)
    (nat_mul_bar A.k) hlev G).exists
  choose pl hpl using hpull
  have hmv : ∀ (u : ptO Xo (xOf y) ⟶ Xo.univ.t.G) G G', u ^ ((A.k * N) ^ 2) = 1 → Moves Xo (u ^ A.k) G G' →
      Moves Xo u (pl G) (pl G') := fun u G G' hu h =>
    moves_of_pulls E H Dw l Xo _ (xOf y) (A.k : 𝓞 E) (A.k ^ 2) (N ^ 2) ((A.k * N) ^ 2) (nat_mul_bar A.k) hlev
      hkN.pow _ u (comp_act_nat Xo u A.k) hu G G' _ _ h (hpl G) (hpl G')
  have hsub : Ideal.span {((A.k * N : ℕ) : 𝓞 E)} • stdLat E n ≤ Λ.La := by
    refine le_trans (Submodule.smul_mono_left ?_) (hL.2.2.trans inf_le_left)
    rw [Nat.cast_mul]
    exact Ideal.span_singleton_le_span_singleton.2 (dvd_mul_left _ _)
  have hiso := (GlobalTheory.zh_isotropic_and_half_isotropic GlobalTheory.firstFiveLaws.1 E H Dw l Xo _ (xOf y) n Λ (A.k * N) hU
    hkN.pos hsub).1
  obtain ⟨hff, -, hhom⟩ := GlobalTheory.PushIntegral.map_pushL_mem_FFV E H Dw l c n Λ w P hP T io A.k A.ga
    (isUnit_of_coprime hl A.cop) A.unitary A.into
  have hkN0 : ((A.k * N : ℕ) : c.F) ^ P.totalDegree ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hkN.pos.ne')
  obtain ⟨z, hz1, hz2⟩ := GlobalTheory.T.sum_hv_primary_kernel_alt E H Dw l Xo c hst T io y C hC nab hnab e ρ w n he hB ℓ hp hl (A.k * N)
    (A.k ^ 2) (N ^ 2) A.k₁ A.p A.q ((A.k : 𝓞 E) • A.g) hkN hsim (mul_pow _ _ _) (A.cop.pow_left 2) hR A.cop₁
    (by rw [Matrix.smul_mul, A.gq, smul_smul]; congr 1; push_cast; ring) J a hinj ha'
    (fun i i' ε hε => hiso (a i) (a i') ε (hZ i) (hZ i') fun b => by rw [← Nat.cast_pow]; exact hε b)
    (fun b => pl (F₀ b)) (fun i b => pl (F (π i) b))
    (fun b => .pull (N ^ 2) (A.k ^ 2) _ (A.k : 𝓞 E) (F₀ b) _ (hre b)
      (one_or_four_le hN)
      A.odd.pow (nat_mul_bar A.k) hlev (hpl _))
    (fun b u hu huN => hmv u _ _ (by rw [pow_two, pow_mul, huN, one_pow]) (hfix b _
      (hu.imp fun j hj => by rw [pow_right_comm, hj, one_pow]) (by rw [← pow_mul, huN])))
    (fun i b => hmv _ _ _ ((hZ i).1 b) (by rw [← hπ]; exact hF _ _))
    P (((A.k * N : ℕ) : c.F) ^ P.totalDegree)⁻¹ hP.1
    (by rw [A.prod, hhom, ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ hkN0, map_one, _root_.one_mul]; exact hff)
  have hch : ∀ i, hv Xo c nab y.1 ((A.k * N) ^ 2) (fun b => pl (F (π i) b)) P =
      io (nrm Dw c w (A.k : 𝓞 E)) * hv Xo c nab y.1 (N ^ 2) (F (π i)) P := fun i =>
    GlobalTheory.T.harmonic_value_chain_rule_normalized_pullback E H Dw l Xo c hst nab hnab T.Fr y.1 (A.k : 𝓞 E) (A.k ^ 2) (N ^ 2) _ (nat_mul_bar A.k) hlev n
      (F (π i)) _ (fun b => hpl _) w P hP.1
  obtain ⟨hi1, hi2, -⟩ := GlobalTheory.LatticeIndex.latidx E H Dw l c n Λ N M ℓ hU hL hp A
  have hcnt := GlobalTheory.T.card_primaryTorsionTuples_killed_by_matrix E H Dw l Xo T.Fr (xOf y) ℓ hp n A.q ((N : 𝓞 E) • A.g) A.k₁ (N ^ 2) A.cop₁
    (pow_pos hN.pos 2) (by rw [Matrix.smul_mul, A.gq, smul_smul]; congr 1; push_cast; ring) hR
  rw [card_kills Xo A.p A.q a hinj ha', hcnt, hi1, Finset.sum_congr rfl fun i _ => hch i, ← Finset.mul_sum,
    Equiv.sum_comp π fun i => hv Xo c nab y.1 (N ^ 2) (F i) P] at hz2
  have hδ : 0 ≤ nval T.V e (io (∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ)) :=
    GlobalTheory.ShortBound.nval_nonneg e (map_isIntegral_int io (IsIntegral.prod _ fun τ _ =>
      ((Algebra.IsIntegral.isIntegral (R := ℤ) A.p.det).map (embK c τ).toIntAlgHom).pow _))
  have hz3 : ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ) * z) := by
    rw [nval_mul]
    calc ((-ρ : ℝ) : EReal) = 0 + ((-ρ : ℝ) : EReal) := (zero_add _).symm
      _ ≤ _ := add_le_add hδ hz1
  generalize io (∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ) = δ at hz2 hz3
  have u2 := un_ordProj (K := T.Fr) hp hl hi2
  have u3 := un_nrm (Dw := Dw) c T io hl A.cop w
  have u4 := (un_of_coprime (K := T.Fr) hl A.cop).pow P.totalDegree
  rw [← ((u2.mul u3.inv).mul u4).nval e _] at hz3
  convert hz3 using 2
  have h3 := u3.ne
  have h4 := u4.ne
  have h5 : (N : T.Fr) ^ P.totalDegree ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hN.pos.ne')
  simp only [map_mul, map_inv₀, map_pow io, map_natCast, Nat.cast_mul, mul_pow] at hz2 ⊢
  generalize (∑ i, hv Xo c nab y.1 (N ^ 2) (F i) P) = Sm at *
  generalize io (nrm Dw c w (A.k : 𝓞 E)) = ν at *
  generalize (A.k : T.Fr) ^ P.totalDegree = κ at *
  generalize (N : T.Fr) ^ P.totalDegree = ξ at *
  have h6 : Sm = κ * ξ * ν⁻¹ * ((κ * ξ)⁻¹ * (ν * Sm)) := by field_simp
  rw [h6, hz2]
  field_simp

theorem bound_of_coprime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), Good3 C → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), 0 < e → ChBound C e ρ w n → ∀ (ℓ : ℕ), ℓ.Prime → ¬ IsUnit (ℓ : T.V) → ∀ (Λ : GenLat E n) (N M : ℕ), Λ.Unimod → Λ.LevOK N M → ∀ P : MvPolynomial (LtN Dw n) c.F, P ∈ harmL c Λ w → ∀ (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (tp : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (F : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo (xOf y)))), (∀ i, InZh Xo Λ N (z i)) → GeoInj Xo (xOf y) z → (∀ b, tp b ^ (N ^ 2) = 1) → (∀ i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) (z i b) (tp b) (F i b)) → AllRat Xo (xOf y) (N ^ 2) → (∃ m : ℕ, Nat.Coprime m ℓ ∧ ∀ b, tp b ^ m = 1) → letI := io.toAlgebra; ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) * ∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P) := by
  intro E _ _ _ H Dw l Xo c _ hst T io y C hC nab hnab e ρ w n he hB ℓ hp hl Λ N M hU hL P hP z tp F hz hg
    htp hF hR ⟨m', hm', htm⟩
  letI := io.toAlgebra
  obtain ⟨J, J', _, _, a, a', σ, hinj, ha, ⟨m, hm, ham⟩, hσ, -⟩ :=
    GlobalTheory.T.isotropic_group_primary_decomposition E H Dw l Xo T.Fr (xOf y) n Λ N M ℓ hU hL hp z hz hg
  rw [← Equiv.sum_comp σ, Fintype.sum_prod_type_right, Finset.mul_sum]
  refine GlobalTheory.ShortPrime.le_nval_sum _ _ _ _ fun i' _ => ?_
  choose F₀ h1 h2 h3 using fun b => GlobalTheory.ShortPrime.exists_base Xo hL.1 (sOf1 y) (a' i' b) (tp b) (ham i' b).2 (htp b)
    hm hm' (ham i' b).1 (htm b)
  refine ell_part Xo c hst T io y C hC nab hnab e ρ w n he hB ℓ hp hl Λ N M hU hL P hP hR J a
    hinj ha F₀ (fun i b => sqN Xo N (F (σ (i, i')) b)) h1 h2 fun i b => ?_
  obtain ⟨h4, h5⟩ := (ha _).1 ⟨i, rfl⟩
  exact h3 b _ _ (h5 b) (h4.1 b) (hσ i i' b ▸ hF _ b)

end Coprime

section Triv
open GlobalTheory.PlaceInt.ShortTriv

theorem bound_of_trivAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), Good3 C → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), 0 < e → ChBound C e ρ w n → ∀ (ℓ : ℕ), ℓ.Prime → ¬ IsUnit (ℓ : T.V) → ∀ (Λ : GenLat E n) (N M : ℕ), Λ.Unimod → Λ.LevOK N M → ∀ P : MvPolynomial (LtN Dw n) c.F, P ∈ harmL c Λ w → ∀ (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (tp : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (F : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo (xOf y)))), (∀ i, InZh Xo Λ N (z i)) → GeoInj Xo (xOf y) z → (∀ b, tp b ^ (N ^ 2) = 1) → (∀ i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) (z i b) (tp b) (F i b)) → Λ.TrivAt ℓ → ∀ (n' A Bn j : ℕ) (α β₀ : 𝓞 E), Nat.Coprime n' ℓ → (N : 𝓞 E) = β₀ * α * n' → α * H.bar α = (A : 𝓞 E) → β₀ * H.bar β₀ = (Bn : 𝓞 E) → A * Bn = ℓ ^ j → (∀ b, (tp b ≫ Xo.univ.t.act.act β₀) ^ (n' ^ 2 * A) = 1) → letI := io.toAlgebra; ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (nrm Dw c w α * (((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹)) * ∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P) := by
  intro E _ _ _ H Dw l Xo c _ hst T io y C hC nab hnab e ρ w n he hb ℓ hℓ hlu Λ N M hU hL P hP z tp F hz hg ht hF
    htr n' A Bn j α β₀ hn' hfac hA hB hAB htp
  letI := io.toAlgebra
  have hN : Odd N := hL.1
  obtain ⟨hfz, hm0, hT⟩ := GlobalTheory.T.lattice_trivial_at_prime_indices_and_units E H Dw l c n Λ N M ℓ hU hL hℓ htr
  obtain ⟨-, hFF⟩ := hT T io hlu
  obtain ⟨J, J', _, _, a, a', σ, -, haZ, ⟨m, hm, ha'⟩, hzs, hcard⟩ :=
    GlobalTheory.T.isotropic_group_primary_decomposition E H Dw l Xo T.Fr (xOf y) n Λ N M ℓ hU hL hℓ z hz hg
  have hlev : N ^ 2 = n' ^ 2 * ℓ ^ j := by
    have h2 : (N : 𝓞 E) = H.bar β₀ * H.bar α * n' := by
      have := congrArg H.bar hfac
      simpa only [map_mul, map_natCast] using this
    have h3 : ((N ^ 2 : ℕ) : 𝓞 E) = ((n' ^ 2 * (A * Bn) : ℕ) : 𝓞 E) := by
      push_cast
      rw [← hA, ← hB, sq]
      nth_rewrite 1 [hfac]
      rw [h2]; ring
    rw [← hAB]
    exact_mod_cast h3
  have hUU : ∀ i i' b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) (a' i' b) (tp b) (F (σ (i, i')) b) := by
    intro i i' b
    obtain ⟨hi, hi2⟩ := (haZ (a i)).1 ⟨i, rfl⟩
    obtain ⟨k, hk⟩ := hi2 b
    have h1 := hF (σ (i, i')) b
    rw [hzs] at h1
    exact isUUOver_of_mul Xo hN _ (a i b) (a' i' b) (tp b) (pow_eq_one_of_trivAt Xo htr hi b hk) (ha' i' b).2 (ht b)
      (hm.pow_right k) hk (ha' i' b).1 _ h1
  obtain ⟨i₀⟩ : Nonempty J := Fintype.card_pos_iff.1 (by rw [hcard]; exact pow_pos hℓ.pos _)
  have hsum : ∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P =
      (Fintype.card J : T.Fr) * ∑ i', hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F (σ (i₀, i')) b)) P := by
    rw [← σ.sum_comp, Fintype.sum_prod_type, ← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
    congr 1
    funext b
    exact sqN_eq_of_isUUOver Xo hN _ _ _ (ha' i' b).2 (ht b) _ _ (hUU i i' b) (hUU i₀ i' b)
  have hterm : ∀ i', ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (nrm Dw c w α * ((N : c.F) ^ P.totalDegree)⁻¹) *
      hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F (σ (i₀, i')) b)) P) := fun i' => by
    refine GlobalTheory.T.harmonicValue_translated_product_valuation_bound E H Dw l Xo c hst T io y C hC nab hnab e ρ w n he hb N n' A Bn α β₀ hN hfac hA hB
      (isUnit_of_coprime T hn' hlu) (a' i') tp _ (fun b => ⟨(ha' i' b).2, ht b, ?_, htp b, hUU i₀ i' b⟩) P hP.1
      (hFF w P hP)
    have h1 : (a' i' b ^ (n' ^ 2)) ^ m = 1 := by rw [← pow_mul, _root_.mul_comm, pow_mul, (ha' i' b).1, one_pow]
    have h2 : (a' i' b ^ (n' ^ 2)) ^ (ℓ ^ j) = 1 := by rw [← pow_mul, ← hlev, (ha' i' b).2]
    have h3 := pow_gcd_eq_one.2 ⟨h1, h2⟩
    rw [(hm.pow_right j).gcd_eq_one, pow_one] at h3
    have := Xo.univ.t.act.hom (α * β₀)
    rw [← MonObj.pow_comp, h3, MonObj.one_comp]
  obtain ⟨m', hm'c, hm'⟩ : ∃ m' : ℕ, Nat.Coprime m' ℓ ∧ Λ.mIdx N (Dw.p + Dw.q) = Fintype.card J * m' :=
    ⟨_, (Nat.coprime_ordCompl hℓ hm0).symm, by rw [hcard, hfz, Nat.ordProj_mul_ordCompl_eq_self]⟩
  have hm'u := isUnit_of_coprime T hm'c hlu
  haveI : CharZero T.Fr := algebraRat.charZero _
  have hm'0 : (m' : T.Fr) ≠ 0 := by
    have : m' ≠ 0 := by rintro rfl; simp at hm'u
    exact_mod_cast this
  have hJ0 : (Fintype.card J : T.Fr) ≠ 0 := by
    have : Fintype.card J ≠ 0 := by rw [hcard]; exact (pow_pos hℓ.pos _).ne'
    exact_mod_cast this
  have hre : ∀ s : T.Fr, io (nrm Dw c w α * (((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹)) *
      ((Fintype.card J : T.Fr) * s) =
      ((m' : T.Fr)⁻¹ * (io (nrm Dw c w α * ((N : c.F) ^ P.totalDegree)⁻¹) * s)) := fun s => by
    rw [hm']
    simp only [map_mul, map_inv₀, map_natCast, Nat.cast_mul]
    generalize (io ((N : c.F) ^ P.totalDegree))⁻¹ = q
    field_simp
  rw [hsum, hre,
    nval_mul_unit e (inv_ne_zero hm'0) (vV_inv_eq_zero T (vV_natCast T hm'u)), Finset.mul_sum]
  exact le_nval_sum T _ e _ _ fun i' _ => hterm i'

end Triv

section Point
open GlobalTheory.ShortBound
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem class_bound (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (hst : ∀ a : 𝓞 E, star a = H.bar a)
    (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (hC : Good3 C)
    (nab : NabV Xo c) (hnab : IsNab Xo c nab) (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (he : 0 < e)
    (hch : ChBound C e ρ w n) (ℓ : ℕ) (hℓ : ℓ.Prime) (hu : ¬ IsUnit (ℓ : T.V)) (Λ : GenLat E n) (N : ℕ)
    (hΛ : Λ.Unimod) (hT : Λ.TrivAt l.M) (hN : Λ.LevOK N l.M)
    (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmL c Λ w)
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G))
    (tp : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G))
    (F : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo (xOf y))))
    (hz : ∀ i, InZh Xo Λ N (z i)) (hg : GeoInj Xo (xOf y) z) (a : Fin n → Dw.La)
    (htp : ∀ b, tp b ^ N = levPt Xo (xOf y) (a b) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp b))
    (hF : ∀ i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) (z i b) (tp b) (F i b))
    (hR : AllRat Xo (xOf y) (N ^ 2)) (hsq : ¬ ℓ ^ 2 ∣ l.M) (α : 𝓞 E)
    (hα : (¬ ℓ ∣ l.M ∧ α = 1) ∨ (ℓ ∣ l.M ∧ α * H.bar α = (ℓ : 𝓞 E) ∧ l.Mb ≤ Ideal.span {H.bar α}) ∨
      (ℓ ∣ l.M ∧ α = (ℓ : 𝓞 E))) :
    letI := io.toAlgebra
    ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (nrm Dw c w α) *
      io (((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) *
        ∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P) := by
  have hk : ∀ b, KilledBy Xo l.Mb (tp b ^ N) := fun b => by rw [(htp b).1]; exact levPt_killed Xo _ _
  obtain ⟨t1, t2⟩ := GlobalTheory.TorsFac.factorisation E H Dw l Xo N ℓ hN.1 hN.2.1 hℓ
  have lev : ∀ A : ℕ, ℓ ∣ l.M → α * H.bar α = (A : 𝓞 E) →
      ((A = ℓ ∧ l.Mb ≤ Ideal.span {H.bar α}) ∨ (α = (ℓ : 𝓞 E) ∧ ℓ ∣ l.M)) →
      letI := io.toAlgebra
      ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (nrm Dw c w α) *
        io (((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) *
          ∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P) := by
    intro A hd hA hor
    obtain ⟨n', Bn, j, β₀, h1, h2, h3, h4, h5⟩ := t2 α A hA hsq hor
    obtain ⟨k, hk1, hk2⟩ := hT
    rw [← map_mul]
    exact bound_of_trivAt E H Dw l Xo c hst T io y C hC nab hnab e ρ w n he hch ℓ hℓ hu Λ N l.M hΛ hN P hP z tp F
      hz hg (fun b => (h5 _ _ (hk b) (htp b).2).1) hF ⟨k, hk1.coprime_dvd_right hd, hk2⟩ n' A Bn j α β₀ h1 h2 hA h3 h4
      (fun b => (h5 _ _ (hk b) (htp b).2).2)
  rcases hα with ⟨hd, rfl⟩ | ⟨hd, hA, hM⟩ | ⟨hd, hA⟩
  · obtain ⟨n', j, -, -, h5⟩ := t1 hd
    rw [nrm_one, map_one, _root_.one_mul]
    choose i hi using fun b => (h5 _ _ (hk b) (htp b).2).2.2
    refine bound_of_coprime E H Dw l Xo c hst T io y C hC nab hnab e ρ w n he hch ℓ hℓ hu Λ N l.M hΛ hN P hP z tp F
      hz hg (fun b => (h5 _ _ (hk b) (htp b).2).1) hF hR ⟨l.M ^ (∑ b, i b),
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hd).symm, fun b => ?_⟩
    obtain ⟨m, hm⟩ : l.M ^ i b ∣ l.M ^ (∑ b, i b) :=
      pow_dvd_pow _ (Finset.single_le_sum (f := i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b))
    rw [hm, pow_mul, hi b, one_pow]
  · exact lev ℓ hd hA (Or.inl ⟨rfl, hM⟩)
  · exact lev (ℓ ^ 2) hd (by rw [hA, map_natCast]; push_cast; ring) (Or.inr ⟨hA, hd⟩)

end Point

section Run
open IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions GlobalTheory.ShortBound

theorem vV_prod_nat (T : CDVR) (s : Finset ℕ) (hs : ∀ p ∈ s, p ≠ 0) :
    vV T.V ((∏ p ∈ s, p : ℕ) : T.Fr) = ∑ p ∈ s, vV T.V (p : T.Fr) := by
  classical
  haveI : CharZero T.Fr := algebraRat.charZero _
  induction s using Finset.induction_on with
  | empty => simpa using vV_one
  | insert a s ha ih =>
    have h1 := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Nat.cast_mul,
      vV_mul (Nat.cast_ne_zero.2 (hs a (Finset.mem_insert_self _ _))) (Nat.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 h1)),
      ih h1]

theorem exists_smul_short_nonneg (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (hlev : d.IsLev)
    (hnab : ∃ _ : StarRing (𝓞 D.host.E), IsNab d.Xo₂ d.c₂ d.nab₂)
    (hroot : ∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y₂ ^ 1 = 1)
    (hsf : Squarefree d.l₂.M) (hph : ∃ ph ψ x₀, d.PhiPin ph ψ x₀) (nab : NabV Xo c) (bad nV : ℕ)
    (w : (D.host.E →+* ℂ) × ℕ → ℕ) (g : Rul Xo c) (hg : g ∈ shortGen Xo c nab bad nV w n d) :
    ∃ s : c.F, s ≠ 0 ∧ ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v (s • g) := by
  obtain ⟨hsec, Λ, N, x0, P, hU, hTb, hTM, hN, hadm, hP, hR⟩ := hg
  obtain ⟨inst, hnab⟩ := hnab
  obtain ⟨ph, ψ, x₀, hph⟩ := hph
  have hβ : betaH (Dw := Dw) c Λ ≠ 0 := by
    unfold betaH
    split_ifs with h
    exacts [h.choose_spec.1, one_ne_zero]
  have hM0 : d.l₂.M ≠ 0 := hsf.ne_zero
  have hc0 : Nat.card (Fin n → LevQ Dw d.l₂) ≠ 0 := by
    rw [GlobalTheory.PlaceInt.card_fun_levQ]; exact pow_ne_zero _ hM0
  have hs0 : ∀ p ∈ D.host.condN.primeFactors, p ≠ 0 := fun p hp =>
    (Nat.prime_of_mem_primeFactors hp).ne_zero
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : ℕ, P₀ = ∏ p ∈ D.host.condN.primeFactors, p := ⟨_, rfl⟩
  have hP0 : P₀ ≠ 0 := hP₀ ▸ Finset.prod_ne_zero_iff.2 hs0
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = P₀ ^ ((NumberField.discr D.host.E).natAbs * Formalism.L2.Pj.DF Dw w) * d.l₂.M ^ Formalism.L2.Pj.DF Dw w *
    Nat.card (Fin n → LevQ Dw d.l₂) := ⟨_, rfl⟩
  have hK0 : K ≠ 0 := hK ▸ mul_ne_zero (mul_ne_zero (pow_ne_zero _ hP0) (pow_ne_zero _ hM0)) hc0
  refine ⟨(K : c.F) * betaH (Dw := Dw) c Λ, mul_ne_zero (Nat.cast_ne_zero.2 hK0) hβ, ?_⟩
  rintro la _ ⟨⟨_, Tc, io, e, ho, yI, hy, eta, heta, rfl⟩, rfl⟩
  show 0 ≤ nval Tc.V e (evI yI _)
  rw [evI_smul]
  have hwi := GlobalTheory.PlaceInt.datum_isIntegral _ _ _ _ Xo c n d hlev ph ψ x₀ hph x0
  obtain ⟨-, ef2, -⟩ := GlobalTheory.PlaceInt.eF_transfer _ _ _ _ Xo c n d Λ
  obtain ⟨T', iT, r, io₂, y₂, C, ζ, z, tp, F, hr, hiT, hfr, hio, hC, hrat, hζ, hz, hgi, htp, hF, hval⟩ :=
    GlobalTheory.PlaceInt.short_value_on_cover _ _ _ _ Xo c n d hlev hnab 1 hroot Λ N hU hTM hN w P hP x0 g hsec hR
      Tc io yI hy
  haveI : CharZero T'.Fr := algebraRat.charZero _
  have he' : 0 < r * e := Nat.mul_pos hr ho.1
  have heR : (0 : ℝ) < ((r * e : ℕ) : ℝ) := by exact_mod_cast he'
  rw [← nval_bc iT hr hiT e, map_mul, hval, ← hio]
  obtain ⟨ℓ, hℓ, hu⟩ := exists_resChar T' hfr
  have hsq : ¬ ℓ ^ 2 ∣ d.l₂.M := fun hd => hℓ.prime.not_unit (hsf ℓ (by rwa [← pow_two]))
  obtain ⟨α, hαM, hα⟩ : ∃ α : ℕ, α ∣ d.l₂.M ∧ ((¬ ℓ ∣ d.l₂.M ∧ (α : 𝓞 D.host.E) = 1) ∨
      (ℓ ∣ d.l₂.M ∧ (α : 𝓞 D.host.E) * H.bar α = (ℓ : 𝓞 D.host.E) ∧ d.l₂.Mb ≤ Ideal.span {H.bar α}) ∨
      (ℓ ∣ d.l₂.M ∧ (α : 𝓞 D.host.E) = (ℓ : 𝓞 D.host.E))) := by
    by_cases hd : ℓ ∣ d.l₂.M
    · exact ⟨ℓ, hd, Or.inr (Or.inr ⟨hd, rfl⟩)⟩
    · exact ⟨1, one_dvd _, Or.inl ⟨hd, Nat.cast_one⟩⟩
  obtain ⟨α', hα'⟩ := hαM
  have ha0 : α ≠ 0 := left_ne_zero_of_mul (hα' ▸ hM0)
  have ha0' : α' ≠ 0 := right_ne_zero_of_mul (hα' ▸ hM0)
  have hch := GlobalTheory.PlaceInt.HostChart.chBound_host D _ Dw _ d.Xo₂ d.c₂ hnab.1 T' io₂ y₂ C (r * e) he' w n _ le_rfl
  haveI := Nat.finite_of_card_ne_zero hc0
  have hu0 : io₂ (nrm Dw d.c₂ w (α : 𝓞 D.host.E)) ≠ 0 :=
    (map_ne_zero io₂).2 (nrm_ne_zero _ _ (Nat.cast_ne_zero.2 ha0))
  have key := le_nval_avg (V := T'.V) (r * e) (fun q => io₂ (d.w x0 q)) _ ζ _
    ((Nat.card (Fin n → LevQ Dw d.l₂) : ℕ) : T'.Fr) _ 1 one_pos hζ hu0 (by exact_mod_cast hc0)
    (fun q => map_isIntegral_int io₂ (hwi q)) _
    (fun q => class_bound d.Xo₂ d.c₂ hnab.1 T' io₂ y₂ C hC _ hnab (r * e) _ w n he' hch ℓ hℓ
      hu Λ N hU hTM hN _ (ef2 _ P hP).1 z (tp q) (F q) hz hgi
      (fun b => levRep (q b)) (htp q) (hF q) hrat hsq α hα)
  have hb0 : io₂ (d.eF (betaH (Dw := Dw) c Λ)) ≠ 0 := (map_ne_zero io₂).2 ((map_ne_zero d.eF).2 hβ)
  have hKv := add_le_add (le_refl (nval T'.V (r * e) (K : T'.Fr))) key
  rw [← nval_mul, nval_of_ne (Nat.cast_ne_zero.2 hK0), ← EReal.coe_add] at hKv
  refine le_trans (EReal.coe_nonneg.2 ?_) (hKv.trans (le_of_eq ?_))
  · have b0 : ∀ p : ℕ, (0 : ℝ) ≤ vV T'.V (p : T'.Fr) := fun p => by
      exact_mod_cast GlobalTheory.PlaceInt.HostChart.vV_nat_nonneg T' p
    have b1 : (vV T'.V (K : T'.Fr) : ℝ) = ((NumberField.discr D.host.E).natAbs * Formalism.L2.Pj.DF Dw w : ℕ) *
        (∑ p ∈ D.host.condN.primeFactors, (vV T'.V (p : T'.Fr) : ℝ)) +
        (Formalism.L2.Pj.DF Dw w : ℕ) * ((vV T'.V (α : T'.Fr) : ℝ) + vV T'.V (α' : T'.Fr)) +
        vV T'.V ((Nat.card (Fin n → LevQ Dw d.l₂) : ℕ) : T'.Fr) := by
      rw [hK, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
        vV_mul (mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hP0)) (pow_ne_zero _ (Nat.cast_ne_zero.2 hM0)))
          (Nat.cast_ne_zero.2 hc0),
        vV_mul (pow_ne_zero _ (Nat.cast_ne_zero.2 hP0)) (pow_ne_zero _ (Nat.cast_ne_zero.2 hM0)),
        vV_pow (Nat.cast_ne_zero.2 hP0), vV_pow (Nat.cast_ne_zero.2 hM0), hP₀, vV_prod_nat T' _ hs0]
      conv_lhs => rw [show ((d.l₂.M : ℕ) : T'.Fr) = (α : T'.Fr) * (α' : T'.Fr) by rw [hα', Nat.cast_mul],
        vV_mul (Nat.cast_ne_zero.2 ha0) (Nat.cast_ne_zero.2 ha0')]
      generalize (NumberField.discr D.host.E).natAbs = A
      push_cast
      ring
    have b2 : (vV T'.V (io₂ (nrm Dw d.c₂ w (α : 𝓞 D.host.E))) : ℝ) = (Formalism.L2.Pj.DF Dw w : ℕ) * vV T'.V (α : T'.Fr) := by
      rw [nrm_nat, map_pow, map_natCast, vV_pow (Nat.cast_ne_zero.2 ha0)]
      push_cast
      ring
    have b3 : ∑ p ∈ D.host.condN.primeFactors, (vV T'.V (p : T'.Fr) : ℝ) / (r * e : ℕ) *
        D.host.vdH p * (Formalism.L2.Pj.DF Dw w : ℝ) / 2 ≤
        ((NumberField.discr D.host.E).natAbs * Formalism.L2.Pj.DF Dw w : ℕ) *
          (∑ p ∈ D.host.condN.primeFactors, (vV T'.V (p : T'.Fr) : ℝ)) / (r * e : ℕ) := by
      rw [Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_le_sum fun p _ => ?_
      have h1 := D.host.vdH_le_natAbs p
      have h2 : (0 : ℝ) ≤ (vV T'.V (p : T'.Fr) : ℝ) / (r * e : ℕ) * (Formalism.L2.Pj.DF Dw w : ℝ) :=
        mul_nonneg (div_nonneg (b0 p) heR.le) (Nat.cast_nonneg _)
      have h3 := mul_le_mul_of_nonneg_left h1 h2
      have h4 := mul_nonneg h2 (show (0 : ℝ) ≤ ((NumberField.discr D.host.E).natAbs : ℝ) by positivity)
      have h5 : (((NumberField.discr D.host.E).natAbs * Formalism.L2.Pj.DF Dw w : ℕ) : ℝ) * (vV T'.V (p : T'.Fr) : ℝ) / (r * e : ℕ) =
          (vV T'.V (p : T'.Fr) : ℝ) / (r * e : ℕ) * (Formalism.L2.Pj.DF Dw w : ℝ) * ((NumberField.discr D.host.E).natAbs : ℝ) := by
        rw [Nat.cast_mul (NumberField.discr D.host.E).natAbs]; ring
      rw [h5]
      linarith
    have b4 : (0 : ℝ) ≤ (Formalism.L2.Pj.DF Dw w : ℕ) * (vV T'.V (α' : T'.Fr) : ℝ) / (r * e : ℕ) :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (b0 _)) heR.le
    rw [b1, b2, add_div, add_div, mul_add, add_div]
    linarith
  · congr 1
    simp only [map_mul, map_inv₀, map_natCast]
    field_simp
end Run

end GlobalTheory.SupFull
