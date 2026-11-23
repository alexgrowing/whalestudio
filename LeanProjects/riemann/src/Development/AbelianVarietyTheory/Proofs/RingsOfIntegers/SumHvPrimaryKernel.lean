import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.InZhIffKillsAdapted
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EqOfSqEqOfOdd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniqueSymmetricTranslateOddLevel
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SumSupportCMul
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ReachedSectionRegularOnIntegralModelStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralChartFormalBiextensionGaugeBoundStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalGroupPointsOfIntegralChartSpecStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SplitKernelFormalGroupOfRationalTorsionStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.KillsFormalPointsIffMemCoordinateKernelStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SumHarmonicValuesFormalKernelSimilitudeStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ShortPlaceB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

set_option autoImplicit false

namespace GlobalTheory.CoreTrace

section Comb

theorem sum_comp_hom {A B K : Type} [Group A] [Group B] [Fintype A] [CommRing K] (φ : A →* B) [Fintype φ.range]
    (g : B → K) : ∑ x : A, g (φ x) = (Nat.card φ.ker : K) * ∑ h : φ.range, g h := by
  classical
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := φ.rangeRestrict), Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => g h) (fun x hx => by
    rw [← (Finset.mem_filter.1 hx).2]; rfl), Finset.sum_const, nsmul_eq_mul]
  congr 2
  obtain ⟨x, rfl⟩ := φ.rangeRestrict_surjective h
  rw [← Nat.card_congr (φ.fiberEquivKer x), ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun a => by simp [Subtype.ext_iff])

theorem sum_cosets {A K : Type} [CommGroup A] [Fintype A] [Field K] [CharZero K] (W₀ W₁ : Subgroup A) [Fintype W₁]
    (f : A → K) (hf : ∀ x, ∀ w ∈ W₀, f (x * w) = f x) (S : K → Prop)
    (hS : ∀ (I : Type) (t : Finset I) (z : I → K), (∀ i ∈ t, S (z i)) → S (∑ i ∈ t, z i)) (s d : K)
    (h : ∀ x, ∃ z, S z ∧ s * ∑ α : W₁, f (α * x) = (Nat.card {α : W₁ // (α : A) ∈ W₀} : K) * d * z) :
    ∃ z, S z ∧ s * ∑ x, f x = (Nat.card W₀ : K) * d * z := by
  classical
  choose z hz hz' using h
  let g : A ⧸ W₀ → K := fun c => f c.out
  have hg : ∀ x : A, g (x : A ⧸ W₀) = f x := fun x => by
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul W₀ x
    simp only [g, hw, hf x w w.2]
  let φ : W₁ →* A ⧸ W₀ := (QuotientGroup.mk' W₀).comp W₁.subtype
  have hker : Nat.card φ.ker = Nat.card {α : W₁ // (α : A) ∈ W₀} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun α => by simp [φ, MonoidHom.mem_ker])
  have hne : (Nat.card φ.ker : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have h1 : ∀ c : A ⧸ W₀, s * ∑ h : φ.range, g (c * h) = d * z c.out := fun c => by
    apply mul_left_cancel₀ hne
    rw [mul_left_comm, ← sum_comp_hom φ (fun b => g (c * b)), ← _root_.mul_assoc, hker, ← hz']
    congr 1
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← hg, QuotientGroup.mk_mul, QuotientGroup.out_eq', _root_.mul_comm]; rfl
  refine ⟨∑ c : (A ⧸ W₀) ⧸ φ.range, z c.out.out, hS _ _ _ fun c _ => hz _, ?_⟩
  have h2 : ∑ x, f x = (Nat.card W₀ : K) * ∑ c : A ⧸ W₀, g c := by
    have := sum_comp_hom (QuotientGroup.mk' W₀) g
    rw [QuotientGroup.ker_mk'] at this
    simp only [QuotientGroup.mk'_apply, hg] at this
    rw [this]
    congr 1
    exact Fintype.sum_bijective (fun c : (QuotientGroup.mk' W₀).range => (c : A ⧸ W₀))
      ⟨Subtype.val_injective, fun c => ⟨⟨c, QuotientGroup.mk'_surjective W₀ c⟩, rfl⟩⟩ _ g fun _ => rfl
  have h3 : ∑ c : A ⧸ W₀, g c = ∑ c : (A ⧸ W₀) ⧸ φ.range, ∑ h : φ.range, g (c.out * h) := by
    rw [← Fintype.sum_prod_type']
    symm
    refine Fintype.sum_bijective (fun p : ((A ⧸ W₀) ⧸ φ.range) × φ.range => p.1.out * p.2) ⟨?_, fun c => ?_⟩ _ _
      fun _ => rfl
    · rintro ⟨c, h⟩ ⟨c', h'⟩ hc
      obtain rfl : c = c' := by
        have := congrArg (QuotientGroup.mk (s := φ.range)) hc
        simpa only [QuotientGroup.mk_mul_of_mem _ h.2, QuotientGroup.mk_mul_of_mem _ h'.2,
          QuotientGroup.out_eq'] using this
      rw [Subtype.ext (mul_left_cancel hc : (h : A ⧸ W₀) = h')]
    · obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul φ.range c
      exact ⟨(c, w⁻¹), by simp [hw]⟩
  rw [h2, h3, mul_left_comm, Finset.mul_sum, Finset.sum_congr rfl fun c _ => h1 _, ← Finset.mul_sum, _root_.mul_assoc]
end Comb

section Move
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {T : CDVR} {x : Sp T.Fr ⟶ Xo.X} {n k : ℕ}

theorem liftFun_mul {S : Scheme.{0}} (A : Over S) {U : Over S} (W : (U ⊗ A).left.Opens) (a b : Γ(U.left, ⊤)) :
    liftFun A W (a * b) = liftFun A W a * liftFun A W b := by
  simp only [liftFun, map_mul]

theorem liftFun_one {S : Scheme.{0}} (A : Over S) {U : Over S} (W : (U ⊗ A).left.Opens) :
    liftFun A W (1 : Γ(U.left, ⊤)) = 1 := by
  simp only [liftFun, map_one]

def Rel (F F' : Fin n → SecN Xo x k) : Prop :=
  ∃ r : Fin n → T.V, ∏ b, r b = 1 ∧ (∀ b, r b ^ k = 1) ∧ ∀ b j, (F' b).f j =
    liftFun Xo.univ.t.G _ (T := ptO Xo x) (toΓ T.Fr (algebraMap T.V T.Fr (r b))) * (F b).f j

theorem Rel.trans {F F' F'' : Fin n → SecN Xo x k} (h : Rel F F') (h' : Rel F' F'') : Rel F F'' := by
  obtain ⟨r, h1, h2, h3⟩ := h
  obtain ⟨r', h1', h2', h3'⟩ := h'
  refine ⟨fun b => r' b * r b, by rw [Finset.prod_mul_distrib, h1, h1', _root_.mul_one],
    fun b => by rw [mul_pow, h2, h2', _root_.mul_one], fun b j => ?_⟩
  rw [h3', h3, map_mul, map_mul, ← _root_.mul_assoc]
  congr 1
  exact (liftFun_mul _ _ _ _).symm

theorem Rel.symm (hk : 0 < k) {F F' : Fin n → SecN Xo x k} (h : Rel F F') : Rel F' F := by
  obtain ⟨r, h1, h2, h3⟩ := h
  refine ⟨fun b => r b ^ (k - 1), by rw [Finset.prod_pow, h1, one_pow],
    fun b => by rw [← pow_mul, _root_.mul_comm, pow_mul, h2, one_pow], fun b j => ?_⟩
  have e : toΓ T.Fr (algebraMap T.V T.Fr (r b ^ (k - 1))) * toΓ T.Fr (algebraMap T.V T.Fr (r b)) = 1 := by
    rw [← map_mul, ← map_mul, ← pow_succ, Nat.sub_add_cancel hk, h2, map_one, map_one]
  rw [h3, ← _root_.mul_assoc]
  refine (_root_.one_mul _).symm.trans ?_
  congr 1
  exact (liftFun_one _ _).symm.trans ((congrArg _ e.symm).trans (liftFun_mul _ _ _ _))

theorem rel_of_moves (hk : Odd k) (u u' : Fin n → (ptO Xo x ⟶ Xo.univ.t.G)) (hu : ∀ b, u b ^ k = 1)
    (hu' : ∀ b, u' b ^ k = 1)
    (hiso : ∀ ε : Fin n → Γ((ptO Xo x).left, ⊤)ˣ,
      (∀ b, WeilIs Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (u b) (u' b) (ε b)) → ∏ b, ε b = 1)
    {F F₁ F₂ F₃ : Fin n → SecN Xo x k} (h₁ : ∀ b, Moves Xo (u' b) (F b) (F₁ b))
    (h₂ : ∀ b, Moves Xo (u b) (F₁ b) (F₂ b)) (h₃ : ∀ b, Moves Xo (u b * u' b) (F b) (F₃ b)) : Rel F₃ F₂ := by
  have hLaw : Laws := GlobalTheory.firstFiveLaws.1
  have := UnivPol.isLocallyNoetherian Xo
  have hw : ∀ b, ∃ ε : Γ((ptO Xo x).left, ⊤)ˣ, WeilIs Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (u b) (u' b) ε :=
    fun b => ((hLaw.weil Xo.X (UnivPol.pol Xo) k (ptO Xo x)).1 (u b) (u' b) (hu b) (hu' b)).exists
  choose ε hε using hw
  choose r hr hrk hF using fun b => moves_mul E H Dw l Xo T.Fr x k hk (u b) (u' b) (ε b) (hu b) (hu' b) (hε b)
  have hint : ∀ b, ∃ v : T.V, algebraMap T.V T.Fr v = r b := fun b =>
    IsIntegrallyClosed.algebraMap_eq_of_integral (IsIntegral.of_pow hk.pos (by rw [hrk]; exact isIntegral_one))
  choose v hv using hint
  have inj := IsFractionRing.injective T.V T.Fr
  have bij : Function.Bijective (toΓ T.Fr) :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of T.Fr)).inv
  have h2 : (∏ b, r b) ^ 2 = 1 := by
    apply bij.1
    rw [map_pow, map_prod, ← Finset.prod_pow, map_one, Finset.prod_congr rfl fun b _ => hr b]
    exact (Units.coe_prod ε Finset.univ).symm.trans (congrArg Units.val (hiso ε hε))
  have hk' : (∏ b, r b) ^ k = 1 := by rw [← Finset.prod_pow]; exact Finset.prod_eq_one fun b _ => hrk b
  refine ⟨v, inj ?_, fun b => inj (by rw [map_pow, hv, hrk, map_one]), fun b j => ?_⟩
  · obtain ⟨t, rfl⟩ := hk
    rw [pow_succ, pow_mul, h2, one_pow, _root_.one_mul] at hk'
    rw [map_prod, map_one, ← hk']
    exact Finset.prod_congr rfl fun b _ => hv b
  · rw [hv]
    exact hF b _ _ _ _ (h₁ b) (h₂ b) (h₃ b) j
end Move

section Ker
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (U : Over Xo.X) {n : ℕ}

def kerSub (mu : Matrix (Fin n) (Fin n) (𝓞 E)) : Subgroup (Fin n → (U ⟶ Xo.univ.t.G)) where
  carrier := {u | Kills Xo mu u}
  one_mem' := by
    letI := ZPart.ptMod Xo U
    refine (ZPart.kills_iff Xo mu _).2 fun i => Finset.sum_eq_zero fun j _ => ?_
    exact smul_zero _
  mul_mem' {u u'} hu hu' := by
    letI := ZPart.ptMod Xo U
    refine (ZPart.kills_iff Xo mu _).2 fun i => ?_
    have h := (ZPart.kills_iff Xo mu _).1 hu i
    have h' := (ZPart.kills_iff Xo mu _).1 hu' i
    simp only [Pi.mul_apply, ofMul_mul, smul_add, Finset.sum_add_distrib, h, h', add_zero]
  inv_mem' {u} hu := by
    letI := ZPart.ptMod Xo U
    refine (ZPart.kills_iff Xo mu _).2 fun i => ?_
    have h := (ZPart.kills_iff Xo mu _).1 hu i
    simp only [Pi.inv_apply, ofMul_inv, smul_neg, Finset.sum_neg_distrib, h, neg_zero]

def primSub (ℓ : ℕ) : Subgroup (Fin n → (U ⟶ Xo.univ.t.G)) where
  carrier := {u | ∀ b, ∃ j : ℕ, u b ^ (ℓ ^ j) = 1}
  one_mem' b := ⟨0, one_pow _⟩
  mul_mem' {u u'} hu hu' b := by
    obtain ⟨i, hi⟩ := hu b
    obtain ⟨j, hj⟩ := hu' b
    refine ⟨i + j, ?_⟩
    rw [Pi.mul_apply, mul_pow, pow_add, pow_mul, hi, one_pow, _root_.mul_comm (ℓ ^ i), pow_mul, hj, one_pow,
      _root_.mul_one]
  inv_mem' {u} hu b := (hu b).imp fun j hj => by rw [Pi.inv_apply, inv_pow, hj, inv_one]

variable {Xo U}
theorem pow_eq_one_of_kills {mu mu' : Matrix (Fin n) (Fin n) (𝓞 E)} {m : ℕ}
    (h : mu' * mu = (m : 𝓞 E) • (1 : Matrix (Fin n) (Fin n) (𝓞 E))) {u : Fin n → (U ⟶ Xo.univ.t.G)}
    (hu : Kills Xo mu u) (b : Fin n) : u b ^ m = 1 := by
  letI := ZPart.ptMod Xo U
  have h1 := ((ZPart.kills_iff Xo mu u).1 hu).mul mu'
  rw [h] at h1
  have h2 := h1 b
  rwa [Finset.sum_eq_single b (fun j _ hj => by simp [Matrix.one_apply_ne hj.symm]) (by simp),
    Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, _root_.mul_one, ← ZPart.pow_iff] at h2

theorem pow_eq_one_of_coprime {A : Type} [Group A] {u : A} {k N ℓ j : ℕ} (hc : Nat.Coprime k ℓ)
    (h : u ^ (k * N) = 1) (hj : u ^ (ℓ ^ j) = 1) : u ^ N = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one] at *
  exact (Nat.Coprime.coprime_dvd_left hj (hc.symm.pow_left j)).dvd_of_dvd_mul_left h

theorem adj_mul {mu : Matrix (Fin n) (Fin n) (𝓞 E)} {m : ℕ} (h : IsSim H mu m) :
    (Matrix.of fun j i => H.bar (mu i j)) * mu = (m : 𝓞 E) • (1 : Matrix (Fin n) (Fin n) (𝓞 E)) := by
  ext j k
  have := h j k
  simp only [Matrix.mul_apply, Matrix.of_apply, this, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp
end Ker

theorem exists_cpt {V : Type} [CommRing V] {d : ℕ} (v : Pt V 0 d) : ∃ δ : Fin d → V, cpt δ = v := by
  refine ⟨fun i => MvPowerSeries.constantCoeff (v i), funext fun i => ?_⟩
  ext m
  obtain rfl : m = 0 := Subsingleton.elim _ _
  simp [cpt]

end GlobalTheory.CoreTrace

namespace GlobalTheory
open CoreTrace

theorem sum_hv_primary_kernel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), Good3 C → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), 0 < e → ChBound C e ρ w n → ∀ (ℓ : ℕ), ℓ.Prime → ¬ IsUnit (ℓ : T.V) → ∀ (N k M k₁ : ℕ) (p q g : Matrix (Fin n) (Fin n) (𝓞 E)), Odd N → IsSim H (p * q) (N ^ 2) → N ^ 2 = k * M → Nat.Coprime k ℓ → AllRat Xo (xOf y) M → Nat.Coprime k₁ ℓ → g * q = ((k₁ * N : ℕ) : 𝓞 E) • (1 : Matrix (Fin n) (Fin n) (𝓞 E)) → ∀ (J : Type) [Fintype J] (a : J → Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)), Function.Injective a → (∀ u : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G), (∃ i, a i = u) ↔ (Kills Xo (p * q) u ∧ ∀ b, (∃ j : ℕ, u b ^ (ℓ ^ j) = 1))) → (∀ i i' (ε : Fin n → Γ((ptO Xo (xOf y)).left, ⊤)ˣ), (∀ b, WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N ^ 2 : ℕ) : ℤ) (a i b) (a i' b) (ε b)) → ∏ b, ε b = 1) → ∀ (F : Fin n → SecN Xo (xOf y) (N ^ 2)) (G : J → Fin n → SecN Xo (xOf y) (N ^ 2)), (∀ b, Reach Xo (sOf1 y) (N ^ 2) (F b)) → (∀ b (u : (ptO Xo (xOf y) ⟶ Xo.univ.t.G)), (∃ j : ℕ, u ^ (ℓ ^ j) = 1) → u ^ N = 1 → Moves Xo u (F b) (F b)) → (∀ i b, Moves Xo (a i b) (F b) (G i b)) → ∀ (P : MvPolynomial (LtN Dw n) c.F) (s : c.F), P ∈ HH c w n → MvPolynomial.map io (MvPolynomial.C s * pushL c ((p * q).map (algebraMap (𝓞 E) E)) P) ∈ FFV (Dw := Dw) T w n → letI := io.toAlgebra; ∃ z : T.Fr, ((-ρ : ℝ) : EReal) ≤ nval T.V e z ∧ io s * ∑ i, hv Xo c nab y.1 (N ^ 2) (G i) P = (Nat.card {i : J // Kills Xo q (a i)} : T.Fr) * io (∏ τ : E →+* ℂ, embK c τ p.det ^ Dw.mult τ) * z := by
  intro E _ _ _ H Dw l Xo c _ hbar T io y C hC nab hnab e ρ w n he hB ℓ hℓ hℓu N k M k₁ p q g hN hsim hkM hk hM hk₁ hg
    J _ a hinj hrange hiso F G hF hfix hG P s hP hPs
  classical
  letI := io.toAlgebra
  have hodd : Odd (N ^ 2) := hN.pow
  obtain ⟨B, hBT, -⟩ := GlobalTheory.T.integralChart_formalBiextension_gauge_bound E H Dw l Xo c hbar T io y C
  obtain ⟨f1, -, fmul, -, -⟩ := GlobalTheory.T.formal_group_points_of_integral_chart_spec E H Dw l Xo c hbar T io y C B hBT
  have hadj := adj_mul hsim
  have hM0 : 0 < M := Nat.pos_of_ne_zero fun h0 => hodd.pos.ne' (by rw [hkM, h0, Nat.mul_zero])
  have hprim := (GlobalTheory.T.splitKernel_formalGroup_of_rational_torsion E H Dw l Xo c hbar T io y C hC B hBT ℓ hℓ hℓu n (p * q) _ k M hk hM0
    (by rw [hadj, hkM]) hM).2
  let W : Subgroup (Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) := kerSub Xo _ (p * q) ⊓ primSub Xo _ ℓ
  have hW : ∀ u, u ∈ W ↔ ∃ i, a i = u := fun u => (hrange u).symm
  let eq : J ≃ W := Equiv.ofBijective (fun i => ⟨a i, (hW _).2 ⟨i, rfl⟩⟩)
    ⟨fun i j hij => hinj (congrArg Subtype.val hij), fun u => ((hW u).1 u.2).imp fun i hi => Subtype.ext hi⟩
  have ha : ∀ u : W, a (eq.symm u) = u := fun u => congrArg Subtype.val (eq.apply_symm_apply u)
  letI : Fintype W := Fintype.ofEquiv J eq
  have htor : ∀ (u : W) b, u.1 b ^ (N ^ 2) = 1 := fun u b => pow_eq_one_of_kills hadj u.2.1 b
  have hG' : ∀ (u : W) b, Moves Xo (u.1 b) (F b) (G (eq.symm u) b) := fun u b => by
    have := hG (eq.symm u) b
    rwa [ha] at this
  have key : ∀ (u u' : W) {F₀ F₁ F₂ F₃ : Fin n → SecN Xo (xOf y) (N ^ 2)}, (∀ b, Moves Xo (u'.1 b) (F₀ b) (F₁ b)) →
      (∀ b, Moves Xo (u.1 b) (F₁ b) (F₂ b)) → (∀ b, Moves Xo ((u * u').1 b) (F₀ b) (F₃ b)) → Rel F₃ F₂ :=
    fun u u' _ _ _ _ h₁ h₂ h₃ => rel_of_moves hodd u.1 u'.1 (htor u) (htor u')
      (fun ε hε => hiso (eq.symm u) (eq.symm u') ε (by rw [ha, ha]; exact hε)) h₁ h₂ h₃
  have hrel : ∀ {F₀ F₁ : Fin n → SecN Xo (xOf y) (N ^ 2)}, Rel F₀ F₁ →
      hv Xo c nab y.1 (N ^ 2) F₁ P = hv Xo c nab y.1 (N ^ 2) F₀ P := by
    rintro F₀ F₁ ⟨r, h1, -, h3⟩
    rw [(hv_linear E H Dw l Xo c hbar nab hnab T.Fr y.1 n P).1 (N ^ 2) F₀ F₁ (fun b => algebraMap T.V T.Fr (r b)) h3,
      ← map_prod, h1, map_one, _root_.one_mul]
  let W₀ : Subgroup W := (kerSub Xo _ q).subgroupOf W
  have hW₀ : ∀ u : W, u ∈ W₀ → ∀ x : W, Rel (G (eq.symm (x * u))) (G (eq.symm x)) := fun u hu x =>
    key x u (fun b => hfix b _ (u.2.2 b) (by
      obtain ⟨j, hj⟩ := u.2.2 b
      exact pow_eq_one_of_coprime hk₁ (pow_eq_one_of_kills hg hu b) hj)) (hG' x) (hG' (x * u))
  have hmul : ∀ u u' : ptO Xo (xOf y) ⟶ Xo.univ.t.G, (∃ α, FormPt C u α) → (∃ α, FormPt C u' α) →
      ∃ α, FormPt C (u * u') α := by
    rintro u u' ⟨α, h⟩ ⟨α', h'⟩
    obtain ⟨δ, hδ⟩ := exists_cpt (addV B.G.F (cpt α) (cpt α'))
    exact ⟨δ, fmul u u' α α' δ h h' hδ⟩
  have hpow : ∀ u : ptO Xo (xOf y) ⟶ Xo.univ.t.G, (∃ α, FormPt C u α) → ∀ m : ℕ, ∃ α, FormPt C (u ^ m) α := by
    intro u hu m
    induction m with
    | zero => exact ⟨0, by rw [pow_zero]; exact f1⟩
    | succ m ih => rw [pow_succ]; exact hmul _ _ ih hu
  let W₁ : Subgroup W :=
    { carrier := {u | ∀ b, ∃ α, FormPt C (u.1 b) α}
      one_mem' := fun b => ⟨0, f1⟩
      mul_mem' := fun {u u'} hu hu' b => hmul _ _ (hu b) (hu' b)
      inv_mem' := fun {u} hu b => by
        have h1 : u⁻¹.1 b = u.1 b ^ (N ^ 2 - 1) :=
          inv_eq_of_mul_eq_one_left (by rw [← pow_succ, Nat.sub_add_cancel hodd.pos]; exact htor u b)
        rw [h1]
        exact hpow _ (hu b) _ }
  obtain ⟨z, hz, hz'⟩ := sum_cosets W₀ W₁ (fun u => hv Xo c nab y.1 (N ^ 2) (G (eq.symm u)) P)
    (fun x u hu => (hrel (hW₀ u hu x)).symm) (fun z => ((-ρ : ℝ) : EReal) ≤ nval T.V e z)
    (fun I t z h => ReciprocityTheory.ChartRestriction.G.PullbackSections.le_nval_sum e t z _ h) (io s)
    (io (∏ τ : E →+* ℂ, embK c τ p.det ^ Dw.mult τ)) (fun x => by
      choose G' hG'' using fun (α : W₁) b =>
        (existsUnique_moves E H Dw l Xo T.Fr (xOf y) (N ^ 2) hodd (α.1.1 b) (htor α b) (G (eq.symm x) b)).1.exists
      have hr : ∀ α : W₁, Rel (G (eq.symm (α * x))) (G' α) := fun α => key α x (hG' x) (hG'' α) (hG' _)
      obtain ⟨z, hz, hz'⟩ := GlobalTheory.T.sum_harmonicValues_formalKernel_similitude E H Dw l Xo c hbar T io y C hC nab hnab e ρ w n he hB ℓ hℓ hℓu N k M p q hN
        hsim hkM hk hM W₁ (fun α => α.1.1) (Subtype.val_injective.comp Subtype.val_injective)
        (fun u => ⟨by rintro ⟨α, rfl⟩; exact ⟨α.1.2.1, α.2⟩, fun ⟨h1, h2⟩ => by
          choose α hα using h2
          exact ⟨⟨⟨u, h1, hprim α ((GlobalTheory.T.kills_formalPoints_iff_mem_coordinateKernel E H Dw l Xo c hbar T io y C B hBT n _ u α hα).1 h1) u hα⟩,
            fun b => ⟨α b, hα b⟩⟩, rfl⟩⟩)
        (G (eq.symm x)) G'
        (fun b => GlobalTheory.T.reachedSection_regular_on_integralModel E H Dw l Xo c hbar T io y C hC _ _ (Reach.move _ _ _ _ (hF b) (hG' x b))) hG''
        (fun α hα => by
          have h1 := hW₀ α hα x
          rw [_root_.mul_comm] at h1
          obtain ⟨r, h2, -, h3⟩ := (h1.symm hodd.pos).trans (hr α)
          exact ⟨r, h2, h3⟩) P s hP hPs
      refine ⟨z, hz, ?_⟩
      rw [Finset.sum_congr rfl fun α _ => (hrel (hr α)).symm]
      exact hz')
  refine ⟨z, hz, ?_⟩
  have hc : Nat.card {i : J // Kills Xo q (a i)} = Nat.card W₀ := Nat.card_congr (eq.subtypeEquiv fun i => Iff.rfl)
  rw [hc, ← hz', ← eq.sum_comp]
  simp only [Equiv.symm_apply_apply]

end GlobalTheory
