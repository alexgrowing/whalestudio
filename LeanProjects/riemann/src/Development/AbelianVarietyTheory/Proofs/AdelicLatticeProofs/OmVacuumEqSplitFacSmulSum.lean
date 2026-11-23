import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NotMemSpanOfCommute
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitScalar

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem idem_smul_mem {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {e : AE D}
    (he : e * e = e) : ∀ u ∈ latO S T LS LT fun _ => True, e • u ∈ latO S T LS LT fun _ => True :=
  GlobalTheory.LatticeStable.smul_mem_latO D S T LS LT _ e
    (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he]))

theorem off_smul_mt {e : AE D} {V : HSp D} {g : GA D V} (hg : SuppAt e V g) :
    (1 - (e + cA D e)) • mt V g = (1 - (e + cA D e)) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  have h : (e + cA D e) • (mt V g - 1) = mt V g - 1 := Matrix.ext fun i j => hg i j
  rw [← sub_eq_zero, ← smul_sub, sub_smul, one_smul, h, sub_self]

theorem off_smul_mt_inv {e : AE D} {V : HSp D} {g : GA D V} (hg : SuppAt e V g) :
    (1 - (e + cA D e)) • mt V g⁻¹ = (1 - (e + cA D e)) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  have h : mt V g * mt V g⁻¹ = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  rw [← h, ← Matrix.smul_mul, off_smul_mt hg, Matrix.smul_mul, Matrix.one_mul]

theorem off_smul_actO {e : AE D} {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h) (u : WO S T) :
    (1 - (e + cA D e)) • actO S T g h u = (1 - (e + cA D e)) • u := by
  unfold actO
  rw [← Matrix.smul_mul, ← Matrix.smul_mul, off_smul_mt hh, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul,
    ← Matrix.mul_smul, off_smul_mt_inv hg, Matrix.mul_smul, Matrix.mul_one]

theorem compAt_mt {e : AE D} (he : IsSplitIdem D e) {V : HSp D} {g : GA D V} (hg : SuppAt e V g) (θ : InfFam D)
    (τ : D.what₂.Tau) : compAt θ τ (mt V g) = 1 := by
  refine Matrix.ext fun i j => ?_
  have h : infPart D ((mt V g - 1) i j) = 0 := by
    rw [← hg i j, RingHom.map_mul, RingHom.map_add, infPart_splitIdem he,
      infPart_splitIdem (isSplitIdem_conj he), add_zero, zero_mul]
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at h
  show θ τ (infPart D (mt V g i j)) = _
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [RingHom.map_one, RingHom.map_one]
  · rw [RingHom.map_zero, RingHom.map_zero]

theorem pairNorm_smul {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (c : ℝ) (f : Mx D m n → ℂ) :
    nrm2 μ 𝓕 ((c : ℂ) • f) = c ^ 2 * nrm2 μ 𝓕 f := by
  unfold nrm2
  rw [← integral_const_mul]
  congr 1
  funext w
  rw [Pi.smul_apply, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem reps_eq {Λ Λ' : AddSubgroup (WO S T)} {e : AE D} {R : Finset (WO S T)}
    (hR : ∀ u ∈ R, u ∈ Λ' ∧ IsHalf e u) (hRu : ∀ u ∈ Λ', IsHalf e u → ∃! v, v ∈ R ∧ u - v ∈ Λ)
    {u v : WO S T} (hu : u ∈ R) (hv : v ∈ R) (h : u - v ∈ Λ) : u = v :=
  (hRu u (hR u hu).1 (hR u hu).2).unique ⟨hu, by rw [sub_self]; exact zero_mem _⟩ ⟨hv, h⟩

theorem sum_sub_notMem {Λ Λ' : AddSubgroup (WO S T)} {e : AE D} (he : IsSplitIdem D e)
    (hst : ∀ u ∈ Λ, e • u ∈ Λ) (hstc : ∀ u ∈ Λ, cA D e • u ∈ Λ) {R R' : Finset (WO S T)}
    (hR : ∀ u ∈ R, u ∈ Λ' ∧ IsHalf e u) (hRu : ∀ u ∈ Λ', IsHalf e u → ∃! v, v ∈ R ∧ u - v ∈ Λ)
    (hR' : ∀ u ∈ R', u ∈ Λ' ∧ IsHalf (cA D e) u) (hRu' : ∀ u ∈ Λ', IsHalf (cA D e) u → ∃! v, v ∈ R' ∧ u - v ∈ Λ)
    {u v u' v' : WO S T} (hu : u ∈ R) (hv : v ∈ R) (hu' : u' ∈ R') (hv' : v' ∈ R') (hne : (u, u') ≠ (v, v')) :
    u + u' - (v + v') ∉ Λ := by
  intro hmem
  have e1 : u + u' - (v + v') = (u - v) + (u' - v') := by abel
  have a1 := (isHalf_iff _ _).1 (isHalf_sub (hR _ hu).2 (hR _ hv).2)
  have a2 := (isHalf_iff _ _).1 (isHalf_sub (hR' _ hu').2 (hR' _ hv').2)
  have b1 : e • (u' - v') = 0 := by rw [← a2, smul_smul, he.2.1, zero_smul]
  have b2 : cA D e • (u - v) = 0 := by rw [← a1, smul_smul, mul_comm, he.2.1, zero_smul]
  have c1 := hst _ hmem
  have c2 := hstc _ hmem
  rw [e1, smul_add, a1, b1, add_zero] at c1
  rw [e1, smul_add, a2, b2, zero_add] at c2
  exact hne (by rw [reps_eq hR hRu hu hv c1, reps_eq hR' hRu' hu' hv' c2])

theorem form_sum {Λ Λ' : AddSubgroup (WO S T)} {e : AE D} (he : IsSplitIdem D e)
    (hd : ∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ Λ ↔ ∀ u' ∈ Λ, ψ (symplO S T u u') = 1))
    (hdd : ∀ u ∈ Λ', ∀ u' ∈ Λ', ψ (symplO S T u u') = 1)
    (hstc : ∀ u ∈ Λ, cA D e • u ∈ Λ) {R R' : Finset (WO S T)}
    (hR : ∀ u ∈ R, u ∈ Λ' ∧ IsHalf e u) (hRu : ∀ u ∈ Λ', IsHalf e u → ∃! v, v ∈ R ∧ u - v ∈ Λ)
    (hR' : ∀ u ∈ R', u ∈ Λ' ∧ IsHalf (cA D e) u) {f : WO S T → ℂ} (hf : IsLatVac (heisO ψ S T) Λ f)
    (hth : ∀ u : WO S T, IsHalf e u → IsThetaFunO ψ S T (heisO ψ S T u f)) {ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ}
    (hℓ : ∀ y, IsHalf (cA D e) y → ∀ φ, IsThetaFunO ψ S T φ → ℓ (heisO ψ S T y φ) = ℓ φ) :
    ℓ (∑ u ∈ R, ∑ u' ∈ R', heisO ψ S T u (heisO ψ S T u' f)) = R'.card * ℓ f := by
  have he' := isSplitIdem_conj he
  obtain ⟨v₀, ⟨hv₀, hv₀Λ⟩, hv₀u⟩ := hRu 0 (zero_mem _) (isHalf_zero e)
  have h1 : ∀ u ∈ R, ℓ (∑ u' ∈ R', heisO ψ S T u (heisO ψ S T u' f)) = R'.card * ℓ (heisO ψ S T u f) := by
    intro u hu
    rw [map_sum, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun u' hu' => ?_
    rw [heisO_comm, hdd _ (hR u hu).1 _ (hR' u' hu').1, one_smul, hℓ _ (hR' u' hu').2 _ (hth u (hR u hu).2)]
  have hv₀' : v₀ ∈ Λ := by rwa [zero_sub, neg_mem_iff] at hv₀Λ
  rw [map_sum, Finset.sum_congr rfl h1, Finset.sum_eq_single_of_mem v₀ hv₀, hf.2 e he v₀ hv₀' (hR _ hv₀).2]
  intro u hu hne
  have huΛ : u ∉ Λ := fun huΛ => hne (hv₀u u ⟨hu, by rwa [zero_sub, neg_mem_iff]⟩)
  obtain ⟨l, hl, hlh, hlne⟩ := exists_dual_half he hd hstc (hR u hu).2 huΛ
  have h2 := hℓ l hlh _ (hth u (hR u hu).2)
  rw [heisO_comm, hf.2 _ he' l hl hlh, map_smul, smul_eq_mul] at h2
  have h3 : (ψ (symplO S T l u) - 1) * ℓ (heisO ψ S T u f) = 0 := by rw [sub_mul, h2, one_mul, sub_self]
  rw [(mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hlne), mul_zero]

theorem om_vacuum_eq_splitFac_smul_sum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → S.SigOK → T.SigOK → ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC S ΛS' → IsSelfDualC T ΛT → IsSelfDualC T ΛT' → ∀ (e : AE D), IsSplitIdem D e → ∀ (g : GA D S) (h : GA D T), SuppAt e S g → SuppAt e T h → ∀ x y, IsDetAt e S g x → IsDetAt e T h y → (∀ u : WO S T, u ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ ∃ u₀ ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), u = actO S T g h u₀) → ∀ (R R' : Finset (WO S T)), (∀ u ∈ R, u ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ IsHalf e u) → (∀ u ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True), IsHalf e u → ∃! v, v ∈ R ∧ u - v ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) → (∀ u ∈ R', u ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ IsHalf (cA D e) u) → (∀ u ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True), IsHalf (cA D e) u → ∃! v, v ∈ R' ∧ u - v ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) → ∀ f, IsVacO ψ θ S T sS sT ΛS ΛT f → om (g, h) f = ((splitFacO χS χT x y : ℂ) * ((Real.sqrt ((R.card : ℝ) * R'.card) : ℝ) : ℂ)⁻¹) • ∑ u ∈ R, ∑ u' ∈ R', heisO ψ S T u (heisO ψ S T u' f) := by
  intro D ψ θ S T χS χT om hW hθ hS hT sS sT hsS hsT ΛS ΛS' ΛT ΛT' hΛS hΛS' hΛT hΛT' e he g h hg hh x y hx hy hmove
    R R' hR hRu hR' hRu' f hf
  classical
  have he' := isSplitIdem_conj he
  have hψ := hW.std
  obtain ⟨hd, -, hsign⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hΛS hΛT
  obtain ⟨hd', -, -⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS' ΛT' hψ hΛS' hΛT'
  have hom := GlobalTheory.WeilVacMove.isVacO_om D ψ θ S T χS χT om hW hθ sS sS sT sT _ _ _ _ g h
    (fun τ => by rw [compAt_mt he hg, mul_one, one_mul]) (fun τ => by rw [compAt_mt he hh, mul_one, one_mul])
    hmove f hf
  have hst := @idem_smul_mem D S T ΛS ΛT _ he.1
  have hstc := @idem_smul_mem D S T ΛS ΛT _ he'.1
  have hst' := @idem_smul_mem D S T ΛS' ΛT' _ he.1
  have hstc' := @idem_smul_mem D S T ΛS' ΛT' _ he'.1
  have hfin' := @latO_fin D S T ΛS' ΛT'
  have huniq := fun F (hF : IsVacO ψ θ S T sS sT ΛS' ΛT' F) =>
    GlobalTheory.VacUnique.vacUniqueO D ψ θ hψ hθ S T sS sT hS hT hsS hsT ΛS' ΛT' hΛS' hΛT' F _ hF hom
  obtain ⟨-, hf⟩ := hf
  unfold IsVacO at huniq
  generalize (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) = Λ at *
  generalize (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True) = Λ'
    at *
  have hdd : ∀ u ∈ Λ', ∀ u' ∈ Λ', ψ (symplO S T u u') = 1 := fun u hu => (hd' u (hfin' hu)).1 hu
  have hoff : ∀ u ∈ Λ', (1 - (e + cA D e)) • u ∈ Λ := by
    intro u hu
    obtain ⟨u₀, hu₀, rfl⟩ := (hmove u).1 hu
    rw [off_smul_actO hg hh, sub_smul, add_smul, one_smul]
    exact sub_mem hu₀ (add_mem (hst _ hu₀) (hstc _ hu₀))
  obtain ⟨F, hFdef⟩ : ∃ F, F = ∑ u ∈ R, ∑ u' ∈ R', heisO ψ S T u (heisO ψ S T u' f) := ⟨_, rfl⟩
  rw [← hFdef]
  have hFlat : IsLatVac (heisO ψ S T) Λ' F := hFdef ▸ isLatVac_sum he hdd hst' hstc' hoff hR hRu hR' hRu' hf.lat
  have hF : F = ∑ p ∈ R ×ˢ R', ψ (symplOH S T p.1 p.2) • heisO ψ S T (p.1 + p.2) f := by
    rw [Finset.sum_product]
    simp only [hFdef, heisO_heisO]
  have hafin : ∀ p ∈ R ×ˢ R', (p.1 + p.2).map (infPart D) = 0 := fun p hp =>
    hfin' (add_mem (hR _ (Finset.mem_product.1 hp).1).1 (hR' _ (Finset.mem_product.1 hp).2).1)
  obtain ⟨v₀, ⟨hv₀, -⟩, -⟩ := hRu 0 (zero_mem _) (isHalf_zero e)
  obtain ⟨v₁, ⟨hv₁, -⟩, -⟩ := hRu' 0 (zero_mem _) (isHalf_zero _)
  have hcR : (0 : ℝ) < R.card := Nat.cast_pos.2 (Finset.card_pos.2 ⟨v₀, hv₀⟩)
  have hcR' : (0 : ℝ) < R'.card := Nat.cast_pos.2 (Finset.card_pos.2 ⟨v₁, hv₁⟩)
  have hN : 0 < (R.card : ℝ) * R'.card := mul_pos hcR hcR'
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (Real.sqrt ((R.card : ℝ) * R'.card))⁻¹ := ⟨_, rfl⟩
  have ht0 : 0 < t := ht ▸ inv_pos.2 (Real.sqrt_pos.2 hN)
  have htF : (t : ℂ) • F = ∑ p ∈ R ×ˢ R', ((t : ℂ) * ψ (symplOH S T p.1 p.2)) • heisO ψ S T (p.1 + p.2) f := by
    rw [hF, Finset.smul_sum]
    simp only [smul_smul]
  have hnorm : ∀ μ 𝓕, IsCovolOne (ratL T S) μ 𝓕 → nrm2 μ 𝓕 F = (R.card : ℝ) * R'.card := by
    intro μ 𝓕 hμ
    rw [hF, GlobalTheory.HeisOrtho.thetaNormSq_sum_heisenbergTranslates_distinctChars D ψ S T hψ.1 μ 𝓕 hμ f hf.theta (hf.norm.2 (μ, 𝓕) hμ) _ _ _ _
      (fun p _ => hψ.1.2.1 _) ?_, Finset.card_product, Nat.cast_mul]
    rintro ⟨u, u'⟩ hp ⟨v, v'⟩ hq hne
    obtain ⟨hu, hu'⟩ := Finset.mem_product.1 hp
    obtain ⟨hv, hv'⟩ := Finset.mem_product.1 hq
    have hm : u + u' - (v + v') ∈ Λ' :=
      sub_mem (add_mem (hR _ hu).1 (hR' _ hu').1) (add_mem (hR _ hv).1 (hR' _ hv').1)
    have hnot : u + u' - (v + v') ∉ Λ := sum_sub_notMem he hst hstc hR hRu hR' hRu' hu hv hu' hv' hne
    rw [hd _ (hfin' hm)] at hnot
    push Not at hnot
    obtain ⟨l, hl, hne'⟩ := hnot
    obtain ⟨ε, hε, hεf⟩ := hsign f hf.lat l hl
    exact ⟨l, ε, by rcases hε with rfl | rfl <;> simp, hεf f hf.lat, hne'⟩
  obtain ⟨c, hc, hcF⟩ := huniq ((t : ℂ) • F) ⟨hψ,
    { inf := hθ
      theta := htF ▸ GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hψ.1 f hf.theta _ _ _ _ hafin
      lat := ⟨fun u hu => by rw [heisO_smul, hFlat.1 u hu],
        fun e₁ he₁ u hu hue => by rw [heisO_smul, hFlat.2 e₁ he₁ u hu hue]⟩
      fock := fun τ => htF ▸ GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ S T hψ.1 hθ f hf.theta τ _ (hf.fock τ) _ _ _ _ hafin
      norm := ⟨hf.norm.1, fun p hp => by
        beta_reduce
        rw [pairNorm_smul, hnorm _ _ hp, ht, inv_pow, Real.sq_sqrt hN.le, inv_mul_cancel₀ hN.ne']⟩ }⟩
  have hf0 : f ≠ 0 := by
    rintro rfl
    obtain ⟨p, hp⟩ := hf.norm.1
    have := hf.norm.2 p hp
    simp [nrm2] at this
  obtain ⟨ℓ, hℓ0, hℓ⟩ := exists_invariant_form he' hd
    (by rw [GlobalTheory.DualPairCheck.cA_cA]; exact hst) hf0 hf.lat
  obtain ⟨r, hr, hrℓ⟩ := hW.om_split e he g h hg hh x y hx hy
  have hval := hrℓ ℓ (fun u hu φ hφ => hℓ u hu φ hφ) f hf.theta
  have hth : ∀ u : WO S T, IsHalf e u → IsThetaFunO ψ S T (heisO ψ S T u f) := by
    intro u hu
    have := GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hψ.1 f hf.theta Unit {()} (fun _ => u) (fun _ => 1) fun _ _ => half_fin he hu
    rwa [Finset.sum_singleton, one_smul] at this
  have hℓF : ℓ F = R'.card * ℓ f := hFdef ▸ form_sum he hd hdd hstc hR hRu hR' hf.lat hth hℓ
  rw [hcF, map_smul, map_smul, hℓF, smul_eq_mul, smul_eq_mul] at hval
  have h4 : c * ((t * R'.card : ℝ) : ℂ) = (r : ℂ) * (splitFacO χS χT x y : ℂ) := by
    apply mul_right_cancel₀ hℓ0
    rw [← hval]
    push_cast
    ring
  have h5 : t * R'.card = r := by
    have := congrArg norm h4
    rwa [norm_mul, norm_mul, hc, Circle.norm_coe, one_mul, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (mul_pos ht0 hcR').le, Real.norm_of_nonneg hr.le] at this
  rw [h5, mul_comm] at h4
  have h6 : c = splitFacO χS χT x y := mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hr.ne') h4
  rw [hcF, h6, smul_smul, ht, Complex.ofReal_inv]

end GlobalTheory.SplitScalar

end
