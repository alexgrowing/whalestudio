import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsRatSecOfPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuativeExtensionPoint

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.BddFin

open SmallSec

variable {F : Type} [Field F] [NumberField F]

theorem exists_denom {O R K : Type} [CommRing O] [IsDomain O] [CommRing R] [CommRing K] (ρ : O →+* R) (ι : R →+* K)
    (h : K) (hgen : ∀ P : Ideal R, P.IsPrime → P.comap ρ = ⊥ → ∃ a ∉ P, ∃ b, ι a * h = ι b) :
    ∃ a : O, a ≠ 0 ∧ ∃ b, ι (ρ a) * h = ι b := by
  by_contra hne
  let I : Ideal R :=
    { carrier := {a | ∃ b, ι a * h = ι b}
      add_mem' := fun ⟨b, hb⟩ ⟨c, hc⟩ => ⟨b + c, by rw [map_add, add_mul, hb, hc, map_add]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := fun c _ ⟨b, hb⟩ => ⟨c * b, by rw [smul_eq_mul, map_mul, mul_assoc, hb, map_mul]⟩ }
  obtain ⟨P, hP, hIP, hd⟩ := Ideal.exists_le_prime_disjoint I ((nonZeroDivisors O).map ρ)
    (Set.disjoint_left.2 fun _ hI ⟨a, ha, e⟩ => hne ⟨a, nonZeroDivisors.ne_zero ha, e ▸ hI⟩)
  obtain ⟨a, ha, hb⟩ := hgen P hP (eq_bot_iff.2 fun a ha => by
    by_contra h0
    exact Set.disjoint_left.1 hd ha ⟨a, mem_nonZeroDivisors_of_ne_zero h0, rfl⟩)
  exact ha (hIP hb)

theorem exists_bound_affine {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp (𝓞 F)) {W : X.Opens} (hW : IsAffineOpen W)
    {x : X} (hxW : x ∈ W) (h : X.functionField) (hgen : ∀ z ∈ W, (p z).asIdeal = ⊥ → RegAt z h) :
    ∃ a : 𝓞 F, a ≠ 0 ∧ ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (yt : Sp e.O ⟶ X),
      (spMap e.O.subtype ≫ yt) ≫ p =
        spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F) →
      RegAt (below (spMap e.O.subtype ≫ yt)) h → ⊤ ≤ yt ⁻¹ᵁ W →
      NumberField.HeightOneSpectrum.adicAbv F v a * e.w (valAt (spMap e.O.subtype ≫ yt) h) ≤ 1 := by
  let ρ := Spec.preimage (hW.fromSpec ≫ p)
  have hρ : Spec.map ρ = hW.fromSpec ≫ p := Spec.map_preimage _
  have hP (P : PrimeSpectrum Γ(X, W)) : (p (hW.fromSpec P)).asIdeal = P.asIdeal.comap ρ.hom :=
    congrArg (fun q : Spec Γ(X, W) ⟶ Sp (𝓞 F) => (q P).asIdeal) hρ.symm
  have hPW (P : PrimeSpectrum Γ(X, W)) : hW.fromSpec P ∈ W := hW.range_fromSpec.le ⟨P, rfl⟩
  obtain ⟨a, ha, b, hab⟩ := exists_denom ρ.hom (fnOf W (gen_mem hxW)) h fun P hPp hP0 => by
    obtain ⟨c, rfl⟩ := hgen _ (hPW ⟨P, hPp⟩) ((hP ⟨P, hPp⟩).trans hP0)
    let := X.presheaf.algebra_section_stalk (⟨_, hPW ⟨P, hPp⟩⟩ : W)
    have := hW.isLocalization_stalk' ⟨P, hPp⟩ (hPW ⟨P, hPp⟩)
    obtain ⟨⟨b, a⟩, e⟩ := @IsLocalization.surj _ _ P.primeCompl _ _ _ this c
    refine ⟨a, a.2, b, ?_⟩
    rw [← algebraMap_germ (hPW ⟨P, hPp⟩), ← algebraMap_germ (hPW ⟨P, hPp⟩), ← map_mul, mul_comm]
    exact congrArg _ e
  refine ⟨a, ha, fun v e yt hy hr hyt => ?_⟩
  have h₁ : below (spMap e.O.subtype ≫ yt) ∈ W :=
    hyt (x := spMap e.O.subtype (IsLocalRing.closedPoint _)) trivial
  have h₂ := (Points.le_preimage_iff _ _).2 h₁
  have h₃ : valAt (spMap e.O.subtype ≫ yt) (fnOf W (gen_mem hxW) (ρ.hom a)) =
      algebraMap F (AlgebraicClosure F) a := by
    rw [valAt_fnOf h₁, Points.valR_eq _ _ h₂]
    have h₄ := Points.specMap_valMap_fromSpec hW _ h₂
    rw [← h₄, Category.assoc, ← hρ, ← Spec.map_comp, ← Spec.map_comp] at hy
    exact congrArg (fun q => q.hom a) (Spec.map_injective hy)
  rw [← e.w_alg, ← h₃, ← map_mul, ← valAt_mul (regAt_fnOf h₁ _ _) hr, hab, valAt_fnOf h₁,
    Points.valR_spMap_comp _ _ _ hyt]
  exact (e.mem_O _).1 (Subtype.coe_prop _)

theorem exists_bound {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] (p : X ⟶ Sp (𝓞 F)) {ι : Type}
    (U : ι → X.Opens) (hU : ∀ x, ∃ i, x ∈ U i) (h : ι → X.functionField)
    (hgen : ∀ i, ∀ z ∈ U i, (p z).asIdeal = ⊥ → RegAt z (h i)) :
    ∃ a : 𝓞 F, a ≠ 0 ∧ ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (yt : Sp e.O ⟶ X),
      (spMap e.O.subtype ≫ yt) ≫ p =
        spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F) →
      ∃ i, ⊤ ≤ yt ⁻¹ᵁ U i ∧ (RegAt (below (spMap e.O.subtype ≫ yt)) (h i) →
      NumberField.HeightOneSpectrum.adicAbv F v a * e.w (valAt (spMap e.O.subtype ≫ yt) (h i)) ≤ 1) := by
  classical
  choose i hi using hU
  choose W hW hxW hWU using fun x => Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (hi x)
  choose a ha hb using fun x => exists_bound_affine p (hW x) (hxW x) (h (i x))
    fun z hz => hgen _ z (hWU x hz)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (W x : Set X)) (fun x => (W x).isOpen)
    fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩
  refine ⟨∏ x ∈ t, a x, Finset.prod_ne_zero_iff.2 fun x _ => ha x, fun v e yt hy => ?_⟩
  obtain ⟨x, hx, hm⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ (yt (IsLocalRing.closedPoint e.O))))
  have h₁ := (Points.le_preimage_iff yt (W x)).2 hm
  refine ⟨i x, h₁.trans (Scheme.Hom.preimage_mono _ (hWU x)), fun hr => le_trans ?_ (hb x v e yt hy hr h₁)⟩
  refine mul_le_mul_of_nonneg_right ?_ (e.w.nonneg _)
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem a hx
  rw [hc, show ((a x * c : 𝓞 F) : F) = a x * c from map_mul (algebraMap (𝓞 F) F) _ _, map_mul]
  exact mul_le_of_le_one_right (AbsoluteValue.nonneg _ _)
    (v.adicAbv_coe_le_one (K := F) (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) c)

theorem nrmFin_pow {C : CxSt F} {Y : Var F} (A : Adl C Y) {k τ : ℕ} {f : Y.Fn} (hf : f ∈ A.secs τ)
    {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (y : AlgPt Y) {g : Y.Fnˣ} (hg : (k • A.D).IsEqn (below y.1) g) {c : ℝ}
    (hl : k * A.lg v e y =
      Real.log (e.w (valAt y.1 (((eqn A.D (below y.1))⁻¹ ^ k * g : Y.Fnˣ) : Y.Fn))) - c) :
    A.nrmFin v τ f e y ^ (A.n * k) =
      e.w (valAt y.1 ((f ^ (A.n : ℕ)) ^ k * g ^ τ)) * Real.exp (-(τ * c)) := by
  have hu : A.D.IsEqn _ (eqn A.D (below y.1)) := Base.isEqn_eqn _ _
  have hw := unitAt_quot hu hg
  have hb := ((hu.nsmul τ).regularAt_iff).1 (Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 hf _)
  have hn : ((A.n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast A.n.ne_zero
  rw [Units.val_pow_eq_pow_val] at hb
  rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val] at hl
  have h₁ : ((A.n * k : ℕ) : ℝ) * (τ * A.lg v e y / ((A.n : ℕ) : ℝ)) = τ * (k * A.lg v e y) := by
    push_cast
    field_simp
  rw [Adl.nrmFin, mul_pow, pow_mul, one_div, Real.rpow_inv_natCast_pow (e.w.nonneg _) A.n.ne_zero,
    ← Real.exp_nat_mul, h₁, hl, mul_sub, sub_eq_add_neg, Real.exp_add, Real.exp_nat_mul,
    Real.exp_log (e.w.pos (valAt_ne_zero hw)), mul_pow_eq _ (eqn A.D (below y.1)) g k τ, pow_mul _ τ k, ← mul_pow,
    valAt_mul (regAt_pow hb _) (regAt_pow hw.regAt _), valAt_pow hw.regAt, valAt_pow hb, map_mul, map_pow, map_pow,
    mul_assoc]

theorem exists_pow_le {C : CxSt F} {Y : Var F} {A : Adl C Y} {M : TrueGeo.Model Y} {L : HermLB M.p} {k : ℕ+}
    {cf : HeightOneSpectrum (𝓞 F) → ℝ} (hA : A.Induced M L k cf) {τ : ℕ} {f : Y.Fn} (hf : f ∈ A.secs τ) :
    ∃ a : 𝓞 F, a ≠ 0 ∧ ∀ v e y, NumberField.HeightOneSpectrum.adicAbv F v a * A.nrmFin v τ f e y ^ (A.n * k : ℕ) ≤
      Real.exp (-(τ * ((k : ℕ) * (A.n : ℕ) * cf v))) := by
  obtain ⟨_, r, hr, -, hfin⟩ := hA
  have := M.ar.isIntegral
  have := isPreimmersion_j M
  have : QuasiCompact M.p := by
    obtain ⟨N, c, hc, h⟩ := M.ar.isProjOver
    have := isProper_str (𝓞 F) N
    rw [← h]
    infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace M.p
  have hη := j_gen_specializes M
  choose t ht using fun i : L.B.ι => fnMap_surjective M.j hη ((f ^ (A.n : ℕ)) ^ (k : ℕ) * (r fun _ => i) ^ τ)
  have hmem {x : Y.X} {i : L.B.ι} (h : M.j x ∈ L.B.U i) :
      x ∈ (L.B.pull M.j).U fun _ => i := Set.mem_iInter.2 fun _ => h
  have hreg (x : Y.X) (i : L.B.ι) (h : M.j x ∈ L.B.U i) : RegAt (M.j x) (t i) := by
    have hu : A.D.IsEqn _ (eqn A.D x) := Base.isEqn_eqn _ _
    have hb := ((hu.nsmul τ).regularAt_iff).1 (Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 hf _)
    rw [Units.val_pow_eq_pow_val] at hb
    rw [← regAt_fnMap_iff M.j hη, ht, ← regAt_iff hu (hr.isEqn _ x (hmem h)), pow_mul, ← mul_pow]
    exact regAt_pow hb _
  obtain ⟨a, ha, hb⟩ := exists_bound M.p L.B.U (exists_chart L.isLB) t fun i z hz h => by
    obtain ⟨z, rfl⟩ := mem_range_j M h
    exact hreg z i hz
  refine ⟨a, ha, fun v e y => ?_⟩
  obtain ⟨yt, h⟩ := exists_lift M e y
  obtain ⟨i, hi, h₁⟩ := hb v e yt (by rw [h, Category.assoc, M.pb.w, ← Category.assoc, y.2])
  have h₂ : M.j (below y.1) ∈ L.B.U i := by
    change below (y.1 ≫ M.j) ∈ _
    rw [← h]
    exact hi (x := spMap e.O.subtype (IsLocalRing.closedPoint _)) trivial
  rw [h] at h₁
  rw [nrmFin_pow A hf e y (hr.isEqn _ _ (hmem h₂)) (hfin v e y yt (fun _ => i) h hi), ← ht,
    valAt_fnMap _ _ _ (hreg _ i h₂), ← mul_assoc]
  exact mul_le_of_le_one_left (Real.exp_pos _).le (h₁ (hreg _ i h₂))

theorem main : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y), A.IsModel → ∀ τ : ℕ, ∀ f ∈ A.secs τ, (∀ v : HeightOneSpectrum (𝓞 F), BddAbove (Set.range fun q : Ext v × AlgPt Y => A.nrmFin v τ f q.1 q.2)) ∧ {v : HeightOneSpectrum (𝓞 F) | ∃ e y, 1 < A.nrmFin v τ f e y}.Finite := by
  intro F _ _ C Y A ⟨M, L, k, cf, hA⟩ τ f hf
  obtain ⟨a, ha, hb⟩ := exists_pow_le hA hf
  have hnk : (A.n * k : ℕ) ≠ 0 := mul_ne_zero A.n.ne_zero k.ne_zero
  refine ⟨fun v => ⟨max 1 (Real.exp (-(τ * ((k : ℕ) * (A.n : ℕ) * cf v))) /
    NumberField.HeightOneSpectrum.adicAbv F v a), ?_⟩, ?_⟩
  · rintro _ ⟨⟨e, y⟩, rfl⟩
    refine (le_total (A.nrmFin v τ f e y) 1).elim le_max_of_le_left fun h => le_max_of_le_right ?_
    have h0 : 0 < NumberField.HeightOneSpectrum.adicAbv F v a := AbsoluteValue.pos _ (by simpa using ha)
    exact (le_self_pow₀ h hnk).trans ((le_div_iff₀' h0).2 (hb v e y))
  · refine ((Ideal.finite_factors (I := Ideal.span {a}) (by simpa using ha)).union hA.1).subset ?_
    rintro v ⟨e, y, h⟩
    by_contra hv
    obtain ⟨h₁, h₂⟩ := not_or.1 hv
    have h₃ : cf v = 0 := not_not.1 h₂
    have h₄ : 1 ≤ NumberField.HeightOneSpectrum.adicAbv F v a := not_lt.1 fun h' => h₁
      (Ideal.dvd_span_singleton.2
        ((v.adicAbv_coe_lt_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) a).1 h'))
    have h₅ := hb v e y
    rw [h₃, mul_zero, mul_zero, neg_zero, Real.exp_zero] at h₅
    exact h₅.not_gt (one_lt_mul_of_le_of_lt h₄ (one_lt_pow₀ h hnk))

end GlobalTheory.TrueGeo.BddFin
