import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CoreEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryPointProperties

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem eig_cont {Γ R K : Type} [TopologicalSpace Γ] [CommRing R] [NormedField K] (I : Ideal R) (y : R →+* K) (a : ℝ)
    (h1 : a < 1) (h0 : 0 ≤ a) (hy : ∀ N, ∀ x ∈ I ^ N, ‖y x‖ ≤ a ^ N) {f : Γ → R} (hf : Alg.AdicCont I f) :
    Continuous fun g => y (f g) := by
  refine continuous_iff_continuousAt.2 fun g => Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨N, hN⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).eventually (gt_mem_nhds hε)).exists
  filter_upwards [(hf N).eventually_eq g] with g' hg'
  rw [dist_eq_norm, ← map_sub]
  exact (hy N _ (Ideal.Quotient.eq.1 hg')).trans_lt hN
private theorem eig_chi_map {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (D : W.GDet n A G) (f : A →+* B)
    (g : G) : (D.map f).chi (MonoidAlgebra.single g 1) = (D.chi (MonoidAlgebra.single g 1)).map f := by
  letI : Algebra A (Polynomial B) := ((algebraMap B (Polynomial B)).comp f).toAlgebra
  let φ : Polynomial A →ₐ[A] Polynomial B :=
    { Polynomial.mapRingHom f with commutes' := fun a => Polynomial.map_C f }
  have h := D.nat (Polynomial A) (Polynomial B) φ
    (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.single g 1))
  refine Eq.trans ?_ h
  change D.D (Polynomial B) _ = D.D (Polynomial B) (MonoidAlgebra.mapRingHom G (Polynomial.mapRingHom f) _)
  congr 1
  simp [map_sub, MonoidAlgebra.mapRingHom_single]
private theorem eig_pol {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (n q : ℕ) (a : ℕ → A) (b : ℕ → B)
    (h : ∀ j ≤ n, f (a j) = b j) : (Hi.heckePol n q a).map f = Hi.heckePol n q b := by
  unfold Hi.heckePol
  rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, map_mul, h j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
  simp
private theorem eig_tele {n : ℕ} {K : Type} [Field K] (f g : Fin n → K) (hg : ∀ i, g i ≠ 0)
    (h : ∀ j, ∏ i with i ≤ j, f i = ∏ i with i ≤ j, g i) (j : Fin n) : f j = g j := by
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    have e : Finset.univ.filter (fun i => i ≤ j) = insert j (Finset.univ.filter fun i => i < j) := by
      ext i; simp [le_iff_eq_or_lt]
    have h1 := h j
    rw [e, Finset.prod_insert (by simp), Finset.prod_insert (by simp),
      Finset.prod_congr rfl fun i hi => ih i (by simpa using hi)] at h1
    exact mul_right_cancel₀ (Finset.prod_ne_zero_iff.2 fun i _ => hg i) h1
private theorem eig_gen {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {S K : Type} [Group S] [Field K] (a : S →* kˣ) (ha : Function.Surjective a) (P Q : S →* K)
    (h1 : ∀ s, a s ∈ Uo k → P s = Q s) (h2 : ∀ s, a s = unif k → P s = Q s) (s : S) : P s = Q s := by
  obtain ⟨t, ht⟩ := ha (unif k)
  have e : s = s * (t ^ ord k (a s))⁻¹ * t ^ ord k (a s) := by group
  have h3 : a (s * (t ^ ord k (a s))⁻¹) ∈ Uo k := by
    rw [map_mul, map_inv, map_zpow, ht, ← div_eq_mul_inv]
    exact GlAx.val_div_ord _
  rw [e, map_mul, map_mul Q, h1 _ h3, map_zpow, map_zpow, h2 t ht]
section Pow
variable {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime] (w : HeightOneSpectrum (𝓞 F))
private theorem eig_ne (hh : (F →+* Qbar l) → ℤ) (x : (w.adicCompletion F)ˣ) : algPow w hh (x : w.adicCompletion F) ≠ 0 := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  haveI := Fintype.ofFinite {j : w.adicCompletion F →+* Qbar l // Continuous j}
  unfold algPow
  rw [finprod_eq_prod_of_fintype]
  exact Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _ ((map_ne_zero j.1).2 x.ne_zero)
private theorem eig_mul (hh : (F →+* Qbar l) → ℤ) (x y : w.adicCompletion F) :
    algPow w hh (x * y) = algPow w hh x * algPow w hh y := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  unfold algPow
  rw [← finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)]
  exact finprod_congr fun j => by rw [map_mul, mul_zpow]
private theorem eig_ht {n : ℕ} (lam : Wt F l n) (i : Fin n) (x : (w.adicCompletion F)ˣ) :
    algPow w (-htW lam i) (x : w.adicCompletion F) * algPow w (lowW lam i) (x : w.adicCompletion F) *
      algPow w (fun _ => 1) (x : w.adicCompletion F) ^ (i : ℕ) = 1 := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  haveI := Fintype.ofFinite {j : w.adicCompletion F →+* Qbar l // Continuous j}
  unfold algPow
  simp only [finprod_eq_prod_of_fintype]
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j _ => ?_
  have h0 : j.1 (x : w.adicCompletion F) ≠ 0 := (map_ne_zero j.1).2 x.ne_zero
  rw [zpow_one, ← zpow_natCast, ← zpow_add₀ h0, ← zpow_add₀ h0]
  simp [htW]
end Pow
private theorem eig_loc (hG : GlobalTheory.Published.GlobalArtinReciprocity) {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver B w)
    (hl : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) (a : Weil h →* (w.adicCompletion F)ˣ) (ha : IsLocalArtin h a) (ι : Qbar l ≃+* ℂ)
    (lam : Wt F l n) (ω : Fin n → (w.adicCompletion F)ˣ →* ℂˣ) (ψ : Fin n → Weil h →* Qbar l)
    (h1 : ∀ i s, a s ∈ Uo _ → ψ i s * (cycBar F Ω l (s : G F Ω) : Qbar l) ^ (i : ℕ) *
      algPow w (lowW lam i) (a s : w.adicCompletion F) = ι.symm (ω i (a s)))
    (h2 : ∀ (j : Fin n) s, a s = Hi.unif _ → ι (∏ i with i ≤ j, ψ i s * (cycBar F Ω l (s : G F Ω) : Qbar l) ^ (i : ℕ)) =
      (ι (∏ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < j + 1,
        algPow w (lowW lam i) ((Hi.unif (w.adicCompletion F) : (w.adicCompletion F)ˣ) : w.adicCompletion F)))⁻¹ * psEig ω (j + 1))
    (i : Fin n) (s : Weil h) : ψ i s = ι.symm (ω i (a s)) * algPow w (-htW lam i) (a s : w.adicCompletion F) := by
  let Q : Weil h →* Qbar l :=
    { toFun := fun s => ι.symm (ω i (a s)) * algPow w (-htW lam i) (a s : w.adicCompletion F)
      map_one' := by simp [algPow]
      map_mul' := fun s t => by
        simp only [map_mul, Units.val_mul, eig_mul]
        ring }
  have he := Loc.epsArt hG h hl a ha
  have hq : ((normV w : ℕ) : Qbar l) ≠ 0 := by
    rw [← resCard_eq_normV]
    exact Nat.cast_ne_zero.2 (Nat.card_pos (α := 𝓀[w.adicCompletion F])).ne'
  refine eig_gen a ha.surj (ψ i) Q (fun s hs => ?_) (fun s hs => ?_) s
  · have hd : deg s = 0 := by
      have := ha.ord_eq s
      rw [ord_eq_zero hs] at this
      omega
    have e1 := h1 i s hs
    rw [he, hd, zpow_zero, one_mul] at e1
    have e2 := eig_ht w lam i (a s)
    change _ = ι.symm (ω i (a s)) * algPow w (-htW lam i) (a s : w.adicCompletion F)
    rw [← e1]
    linear_combination (-ψ i s) * e2
  · have hd : deg s = -1 := by
      have := ha.ord_eq s
      rw [hs, ord_eq_one GlAx.unif_spec] at this
      omega
    have e1 := eig_tele (fun i => ψ i s * (cycBar F Ω l (s : G F Ω) : Qbar l) ^ (i : ℕ))
      (fun i => (algPow w (lowW lam i) (a s : w.adicCompletion F))⁻¹ * (ι.symm (ω i (a s)) * (((normV w : ℕ) : Qbar l) ^ (i : ℕ))⁻¹))
      (fun i => mul_ne_zero (inv_ne_zero (eig_ne w _ _)) (mul_ne_zero ((map_ne_zero ι.symm).2 (Units.ne_zero _))
        (inv_ne_zero (pow_ne_zero _ hq)))) (fun j => ι.injective ?_) i
    · have e2 := eig_ht w lam i (a s)
      have e3 := eig_ne w (lowW lam i) (a s)
      have e4 := pow_ne_zero (i : ℕ) hq
      rw [he, hd, mul_pow, zpow_neg_one, inv_pow] at e1
      change _ = ι.symm (ω i (a s)) * algPow w (-htW lam i) (a s : w.adicCompletion F)
      field_simp at e1
      linear_combination (-ψ i s) * e2 + algPow w (-htW lam i) (a s : w.adicCompletion F) * e1
    · have e : (Finset.univ.filter fun i : Fin n => (i : ℕ) < j + 1) = Finset.univ.filter fun i => i ≤ j := by
        ext i; simp [Nat.lt_succ_iff]
      rw [h2 j s hs, psEig, e, hs, map_prod ι, map_prod ι, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_mul, map_mul, ι.apply_symm_apply, map_inv₀, map_inv₀, map_pow, map_natCast, ← resCard_eq_normV]
      rfl
private theorem eig_det {n : ℕ} {R Γ : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] {l : ℕ} [Fact l.Prime] (y : R →+* Qbar l)
    (D : W.GDet n R Γ) (r : Γ →* GL (Fin n) (Qbar l)) (hr : Continuous r) (S : Set Γ) (hS : Dense S)
    (hD : ∀ i, Continuous fun g => y (D.lam i (MonoidAlgebra.single g 1)))
    (h : ∀ g ∈ S, (D.chi (MonoidAlgebra.single g 1)).map y = (r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly) :
    D.map y = W.GDet.ofRep (W.mat r) := by
  refine AlgebraTools.Det.extDense _ _ S hS (fun i _ => (hD i).congr fun g => ?_)
    (fun i _ => AlgebraTools.Det.repCont _ (Units.continuous_val.comp hr) i) fun g hg => ?_
  · simp [W.GDet.lam, eig_chi_map]
  · rw [eig_chi_map, (AlgebraTools.Det.repApi _).2.1]
    exact h g hg
private theorem eig_ord (hG : GlobalTheory.Published.GlobalArtinReciprocity) {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver B w)
    (hl : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) (a : Weil h →* (w.adicCompletion F)ˣ) (ha : IsLocalArtin h a) (ι : Qbar l ≃+* ℂ)
    (lam : Wt F l n) (ω : Fin n → (w.adicCompletion F)ˣ →* ℂˣ) (hω : ∀ i, IsSmoothChar (ω i)) {R : Type} [CommRing R]
    (y : R →+* Qbar l) (ψ : Fin n → Dec (F := F) B →* Rˣ) (hψ : ∀ i, Continuous fun g => y (ψ i g : R))
    (ε : Dec (F := F) B →* Rˣ) (he : ∀ g, y (ε g : R) = (cycBar F Ω l (g : G F Ω) : Qbar l))
    (t : Fin n → Uo (w.adicCompletion F) → R) (u : Fin n → R)
    (u1 : ∀ i (s : Weil h) (g : Dec (F := F) B) (x : Uo (w.adicCompletion F)), (g : G F Ω) = (s : G F Ω) → a s = x →
      (ψ i g * ε g ^ (i : ℕ) : Rˣ) * t i x = 1)
    (u2 : ∀ (j : Fin n) (s : Weil h) (g : Dec (F := F) B), (g : G F Ω) = (s : G F Ω) → a s = Hi.unif _ →
      ((∏ i with i ≤ j, ψ i g * ε g ^ (i : ℕ) : Rˣ) : R) = u j)
    (h1 : ∀ i (x : Uo (w.adicCompletion F)), (ω i x : ℂ) *
      ι (y (t i x) / algPow w (lowW lam i) ((x : (w.adicCompletion F)ˣ) : w.adicCompletion F)) = 1)
    (h2 : ∀ j : Fin n, ι (y (u j)) = (ι (∏ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < j + 1,
        algPow w (lowW lam i) ((Hi.unif (w.adicCompletion F) : (w.adicCompletion F)ˣ) : w.adicCompletion F)))⁻¹ * psEig ω (j + 1))
    (i : Fin n) : OrdChar ι a (ω i) (htW lam i) (W.pushCh y (ψ i)) := by
  refine ⟨hω i, Units.continuous_iff.2 ⟨hψ i, ((hψ i).comp continuous_inv).congr fun g => by simp⟩, fun s g hg _ => ?_⟩
  obtain rfl : g = Subgroup.inclusion (Weil_le_Dec h) s := Subtype.ext hg
  refine eig_loc hG h hl a ha ι lam ω
    (fun i => ((Units.coeHom _).comp (W.pushCh y (ψ i))).comp (Subgroup.inclusion (Weil_le_Dec h)))
    (fun i s hs => ?_) (fun j s hs => ?_) i s
  · have e1 := congrArg y (u1 i s (Subgroup.inclusion (Weil_le_Dec h) s) ⟨_, hs⟩ rfl rfl)
    have e2 := congrArg ι.symm (h1 i ⟨_, hs⟩)
    rw [map_mul, Units.val_mul, map_mul, Units.val_pow_eq_pow_val, map_pow, he, map_one, Subgroup.coe_inclusion] at e1
    rw [map_mul, ι.symm_apply_apply, map_one, mul_div_assoc', div_eq_one_iff_eq (eig_ne _ _ _)] at e2
    change y (ψ i (Subgroup.inclusion (Weil_le_Dec h) s) : R) * _ * _ = _
    rw [← e2]
    linear_combination (ι.symm (ω i (a s) : ℂ)) * e1
  · refine Eq.trans (congrArg ι (Eq.trans ?_ (congrArg y (u2 j s (Subgroup.inclusion (Weil_le_Dec h) s) rfl hs)))) (h2 j)
    rw [Units.coe_prod, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Units.val_mul, map_mul, Units.val_pow_eq_pow_val, map_pow, he]
    rfl
private theorem eig_pt {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) (R : Type) [CommRing R] [Algebra c.O R] [Alg.IsCO c.O R] :
    Fact (∀ y : R →ₐ[c.O] Qbar l, (∀ (Γ : Type) [TopologicalSpace Γ] (f : Γ → R), Alg.AdicCont (maximalIdeal R) f → Continuous fun g => y.toRingHom (f g)) ∧
      ∀ (v : H.V) (g : Dec (F := L) (H.pl v)), y.toRingHom (H.epsV R v g : R) = (cycBar L Ω l (g : G L Ω) : Qbar l)) := by
  refine ⟨fun y => ?_⟩
  obtain ⟨-, b, b1, b0, hb⟩ := (GradeZeroInterpolatingElement.coPt c R).1 y
  exact ⟨fun Γ _ f hf => eig_cont _ y.toRingHom b b1 b0 hb hf,
    fun v g => (y.commutes (algebraMap ℤ_[l] c.O (cycZ L Ω l (g : G L Ω) : ℤ_[l]))).trans rfl⟩
attribute [-instance] UpperTheory.V.GradeZeroInterpolatingElement.instIsLocalRingSubtypePadicAlgClMemSubalgebraPadicIntO
theorem UpperTheory.V.Hi.core_eigen_of_weight_char_hecke_level :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ), ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)], ∀ (D : W.GDet n (H.TK θ a K) H.Gq) (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ), H.IsUniv θ a K (maximalIdeal _) D ψ →
    ∀ (y : H.TK θ a K →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (Y : H.PartAltAlt ι lam ξ) (F : Fin H.m → H.X.Fn ℂ d), F ∈ Y.Y → F ≠ 0 → (∀ w j, H.opC ι lam d (.inl (w, j)) F = ι (y (H.gen θ a K (.inl (w, j)))) • F) → D.map y.toRingHom = W.GDet.ofRep (W.mat Y.r) ∧ ∀ v (ω : Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ), (∀ i, IsSmoothChar (ω i)) → (∀ i (u : Uo ((H.Sl v).adicCompletion L)), (ω i u : ℂ) * ι (H.finPart θ (y.toRingHom.comp (algebraMap A _)) lam v i u) = 1) → (∀ j : Fin n, ι (y (H.gen θ a K (.inr (v, j)))) = (H.lowVal ι lam v (j + 1))⁻¹ * psEig ω (j + 1)) → ∀ i, OrdChar ι (H.art v) (ω i) (htW lam i) (W.pushCh y.toRingHom (ψ v i)) := by
  intro hN L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ _ ι a K _ _ D ψ hU y lam d ξ Y F hF hF0 hev
  obtain ⟨hc, he⟩ := (eig_pt H (H.TK θ a K)).out y
  refine ⟨eig_det _ D Y.r Y.cont _ hH.dense (fun i => hc _ _ (hU.cont i)) ?_,
    fun v ω hω h1 h2 i => ?_⟩
  · rintro _ ⟨w, hw, B, σ, hB, hσ, rfl⟩
    rw [hU.frob ⟨w, hw⟩ B σ hB hσ]
    refine Polynomial.map_injective ι.toRingHom ι.injective ?_
    rw [Polynomial.map_map]
    refine (eig_pol _ n _ _ (Y.a ⟨w, hw⟩) fun j hj => ?_).trans (Y.frob ⟨w, hw⟩ B σ hB hσ).symm
    unfold HSet.genW
    split_ifs with h
    · have e := hev ⟨w, hw⟩ ⟨j - 1, h.2⟩
      have e' := Y.sph ⟨w, hw⟩ (j - 1 + 1) F hF
      have e2 := smul_left_injective ℂ hF0 (e.symm.trans e')
      rw [show j - 1 + 1 = j by omega] at e2
      exact e2
    · rw [show j = 0 by omega, Y.a_zero, map_one]
  · have h3 := eig_ord hN.aut.art (H.ovr v) (hH.Sl_over v) (H.art v) (hH.art_spec v) ι lam ω hω _ (ψ v)
      (fun i => hc _ _ (hU.ψ_cont v i)) _ (he v)
    have h4 := h3 (fun i x => algebraMap A (H.TK θ a K) (θ (eV n H.Sl v i x))) (fun j => H.gen θ a K (.inr (v, j)))
      (hU.ψ_unit v) (hU.ψ_unif v) h1 h2
    exact h4 i
end
