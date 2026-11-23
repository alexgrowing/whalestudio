import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin

noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Matrix

private theorem fin_reps {A X : Type} [Finite X] (φ : A → X) (r : A → A → Prop) (h : ∀ a b, φ a = φ b → r a b) :
    ∃ S : Finset A, ∀ a, ∃ s ∈ S, r s a := by
  classical
  have hf : (Set.range fun x : Set.range φ => x.2.choose).Finite := Set.finite_range _
  refine ⟨hf.toFinset, fun a => ⟨(⟨φ a, a, rfl⟩ : Set.range φ).2.choose, hf.mem_toFinset.2 ⟨_, rfl⟩, h _ _ ?_⟩⟩
  exact (⟨φ a, a, rfl⟩ : Set.range φ).2.choose_spec

theorem su_abs {Γ G X : Type} [Group Γ] [Group G] [Finite X] (ι : Γ →* G) (Γ₁ : Subgroup Γ) (N K U : Subgroup G) [hN : N.Normal]
    (h₁ : ∀ γ ∈ Γ₁, ι γ ∈ N) (hU : U.relIndex K ≠ 0)
    (hcls : ∃ Y : Finset G, ∀ g, ∃ γ, ∃ y ∈ Y, ∃ k ∈ K, g = ι γ * y * k) (x : G) (P : Γ → Prop) (c : Γ → X)
    (hP : ∀ γ, ∀ k ∈ K, ∀ y, ι γ * (y * k * y⁻¹) ∈ N → P γ)
    (hc : ∀ γ γ', P γ → P γ' → c γ = c γ' → ∃ z, ι z ∈ K ∧ ι z ∈ Subgroup.center G ∧ γ' * γ⁻¹ * z⁻¹ ∈ Γ₁) :
    ∃ S : Finset N, ∀ g : N, ∃ γ ∈ Γ₁, ∃ s ∈ S, ∃ u : N, x⁻¹ * u * x ∈ U ∧ (g : G) = ι γ * s * u := by
  classical
  obtain ⟨Y, hY⟩ := hcls
  choose γ y hy k hk e using fun g : N => hY (g * x)
  let yy : N → Y := fun g => ⟨y g, hy g⟩
  let b : N → N := fun g => Function.invFun yy (yy g)
  have hb : ∀ g, y (b g) = y g := fun g => congrArg Subtype.val (Function.invFun_eq (f := yy) ⟨g, rfl⟩)
  have rel : ∀ g g' : N, y g = y g' → (g' : G) = ι (γ g' * (γ g)⁻¹) * g * (x * ((k g)⁻¹ * k g') * x⁻¹) := by
    intro g g' h
    have e1 : (g : G) = ι (γ g) * y g * k g * x⁻¹ := by rw [← e g]; group
    have e2 : (g' : G) = ι (γ g') * y g * k g' * x⁻¹ := by rw [h, ← e g']; group
    rw [map_mul, map_inv, e1, e2]; group
  have hPg : ∀ g, P (γ g * (γ (b g))⁻¹) := by
    intro g
    refine hP _ _ (mul_mem (inv_mem (hk (b g))) (hk g)) x ?_
    have h := rel (b g) g (hb g)
    have h2 := mul_mem (inv_mem (hN.conj_mem _ (b g).2 (ι (γ g * (γ (b g))⁻¹)))) g.2
    convert h2 using 1
    conv_rhs => rw [h]
    group
  obtain ⟨S₁, hS₁⟩ := fin_reps (fun g : N => (yy g, c (γ g * (γ (b g))⁻¹)))
    (fun g g' => ∃ δ ∈ Γ₁, ∃ w ∈ K, (g' : G) = ι δ * g * (x * w * x⁻¹)) (by
      intro g g' h
      have h1 : yy g = yy g' := congrArg Prod.fst h
      have hbb : b g = b g' := by simp only [b, h1]
      obtain ⟨z, hz, hzc, hz1⟩ := hc _ _ (hPg g) (hPg g') (congrArg Prod.snd h)
      refine ⟨_, hz1, ι z * ((k g)⁻¹ * k g'), mul_mem hz (mul_mem (inv_mem (hk g)) (hk g')), ?_⟩
      have hcm := Subgroup.mem_center_iff.1 hzc ((g : G) * x)
      have := rel g g' (congrArg Subtype.val h1)
      rw [hbb]
      calc (g' : G) = ι (γ g' * (γ g)⁻¹) * (ι z)⁻¹ * (ι z * (g * x)) * ((k g)⁻¹ * k g') * x⁻¹ := by
            conv_lhs => rw [this]
            group
        _ = _ := by
            rw [← hcm]
            simp only [map_mul, map_inv]
            group)
  choose s hs δ hδ w hw e' using hS₁
  have : Finite (K ⧸ U.subgroupOf K) := by
    have : (U.subgroupOf K).FiniteIndex := ⟨hU⟩
    infer_instance
  obtain ⟨S, hS⟩ := fin_reps (fun g : N => ((⟨s g, hs g⟩ : S₁), ((⟨w g, hw g⟩ : K) : K ⧸ U.subgroupOf K)))
    (fun g g' => ∃ δ ∈ Γ₁, ∃ u : N, x⁻¹ * u * x ∈ U ∧ (g' : G) = ι δ * g * u) (by
      intro g g' h
      have h1 : s g = s g' := congrArg Subtype.val (congrArg Prod.fst h)
      have h2 : (w g)⁻¹ * w g' ∈ U := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 (congrArg Prod.snd h :
        ((⟨w g, hw g⟩ : K) : K ⧸ U.subgroupOf K) = (⟨w g', hw g'⟩ : K)))
      have h3 : (g' : G) = ι (δ g' * (δ g)⁻¹) * g * (x * ((w g)⁻¹ * w g') * x⁻¹) := by
        conv_lhs => rw [e' g', ← h1]
        conv_rhs => rw [e' g]
        simp only [map_mul, map_inv]
        group
      have h4 := mul_mem (hδ g') (inv_mem (hδ g))
      refine ⟨_, h4, ⟨x * ((w g)⁻¹ * w g') * x⁻¹, ?_⟩, ?_, h3⟩
      · have h5 := mul_mem (inv_mem (mul_mem (h₁ _ h4) g.2)) g'.2
        convert h5 using 1
        conv_rhs => rw [h3]
        group
      · convert h2 using 1
        group)
  refine ⟨S, fun g => ?_⟩
  obtain ⟨s, hs, δ, hδ, u, hu, e⟩ := hS g
  exact ⟨δ, hδ, s, hs, u, hu, e⟩

section Local

variable {K : Type} [Field K] {Δ : K}

private theorem det_im [CharZero K] (g : DX Δ) : (mt g).det = algebraMap K (Lsq K Δ) (mt g).det.re := by
  have h : GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) g.1 = (wJ Δ)⁻¹ * g.1 * (wJ Δ)⁻¹⁻¹ := g.2
  have h2 := congrArg (fun a : GL (Fin 2) (Lsq K Δ) => ((GeneralLinearGroup.det a : (Lsq K Δ)ˣ) : Lsq K Δ)) h
  simp only [map_mul, map_inv, mul_right_comm _ (GeneralLinearGroup.det g.1), mul_inv_cancel, one_mul] at h2
  have h3 : star (mt g).det = (mt g).det := ((starRingEnd (Lsq K Δ)).map_det (mt g)).trans h2
  have h4 := congrArg QuadraticAlgebra.im h3
  simp only [QuadraticAlgebra.im_star] at h4
  ext
  · simp
  · simp only [QuadraticAlgebra.algebraMap_im]
    linear_combination (-1 / 2 : K) * h4

private theorem det_int {O : Type} [CommRing O] [Algebra O K] {g : DX Δ} (h : g ∈ KD Δ O) : IsIntegral O (mt g).det := by
  obtain ⟨a, ha⟩ := h
  have : mt g = (a : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ))).map (integralClosure O (Lsq K Δ)).val := by
    rw [mt, ← show _ = g.1 from ha]; rfl
  rw [this]
  have h2 := ((integralClosure O (Lsq K Δ)).val : integralClosure O (Lsq K Δ) →+* Lsq K Δ).map_det
    (a : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ)))
  exact h2 ▸ (a : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ))).det.2

private theorem mem_SU {g : DX Δ} : g ∈ SU Δ ↔ (mt g).det = 1 := by
  rw [SU, MonoidHom.mem_ker, ← Units.val_inj]; rfl

variable (Δ) in
private def scal (z : Kˣ) : DX Δ :=
  ⟨GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap K (Lsq K Δ) : K →* Lsq K Δ) z), by
    change GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) _ = (wJ Δ)⁻¹ * _ * (wJ Δ)⁻¹⁻¹
    rw [inv_inv, mul_assoc, eq_inv_mul_iff_mul_eq]
    ext i j : 2
    fin_cases i <;> fin_cases j <;> simp [wJ, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals (ext <;> simp [starRingEnd_apply])⟩

private theorem mt_scal (z : Kˣ) : mt (scal Δ z) = scalar (Fin 2) (algebraMap K (Lsq K Δ) z) := rfl

private theorem scal_KD {O : Type} [CommRing O] [Algebra O K] (u : Oˣ) (g : DX Δ)
    (hg : mt g = scalar (Fin 2) (algebraMap O (Lsq K Δ) u)) : g ∈ KD Δ O := by
  refine ⟨GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap O (integralClosure O (Lsq K Δ)) : O →* _) u), ?_⟩
  refine Units.ext ?_
  change _ = mt g
  rw [hg]
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp

end Local

private theorem loc_glob {F : Type} [Field F] [NumberField F] (t : F) (h : ∀ v : Pl F, IsIntegral (Ov v) (cv v t)) :
    t ∈ (algebraMap (𝓞 F) F).range := by
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one F t fun v => ?_
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 (h v)
  have := a.2
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, show (a : Kv v) = cv v t from ha] at this
  rwa [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v t]

section Global

variable {F : Type} [Field F] [NumberField F] {Δ : F}

private theorem lmap_alg (v : Pl F) (t : F) : lmap (cv v) Δ (algebraMap F (Lsq F Δ) t) = algebraMap (Kv v) _ (cv v t) := by
  ext <;> simp [lmap]

private theorem mem_SA {g : DA Δ} : g ∈ SA Δ ↔ ∀ v, (mt (g.1 v)).det = 1 := by
  rw [SA, Subgroup.mem_iInf]
  exact forall_congr' fun v => mem_SU

private theorem mem_box {g : DA Δ} : g ∈ (rpg _ _).box (fun v : Pl F => KD (cv v Δ) (Ov v)) ↔ ∀ v, g.1 v ∈ KD (cv v Δ) (Ov v) := by
  rw [RPG.box, Subgroup.mem_iInf]; rfl

private theorem det_mul' {K : Type} [Field K] {Δ : K} (a b : DX Δ) : (mt (a * b)).det = (mt a).det * (mt b).det :=
  Matrix.det_mul _ _

private theorem det_inv' {K : Type} [Field K] {Δ : K} (a : DX Δ) : (mt a).det * (mt a⁻¹).det = 1 := by
  rw [← det_mul', mul_inv_cancel]; exact Matrix.det_one

private theorem det_iota {ι : DX Δ →* DA Δ} (hι : IsIotaD ι) (γ : DX Δ) (v : Pl F) :
    (mt ((ι γ).1 v)).det = lmap (cv v) Δ (mt γ).det := by
  rw [hι]; exact ((lmap (cv v) Δ).map_det _).symm

private theorem SA_normal : (SA Δ).Normal := ⟨fun g hg y => mem_SA.2 fun v => by
  change (mt (y.1 v * g.1 v * (y.1 v)⁻¹)).det = 1
  rw [det_mul', det_mul', mem_SA.1 hg v, mul_one, det_inv']⟩

private theorem re_int {ι : DX Δ →* DA Δ} (hι : IsIotaD ι) (γ : DX Δ)
    (h : ∀ v, IsIntegral (Ov v) (mt ((ι γ).1 v)).det) : (mt γ).det.re ∈ (algebraMap (𝓞 F) F).range := by
  refine loc_glob _ fun v => ?_
  have h1 := h v
  rw [det_iota hι, det_im, lmap_alg] at h1
  exact (isIntegral_algebraMap_iff (algebraMap (Kv v) (Lsq (Kv v) (cv v Δ))).injective).1 h1

private theorem unit_det {ι : DX Δ →* DA Δ} (hι : IsIotaD ι) (γ : DX Δ) (k : DA Δ)
    (hk : k ∈ (rpg _ _).box (fun v : Pl F => KD (cv v Δ) (Ov v))) (y : DA Δ) (h : ι γ * (y * k * y⁻¹) ∈ SA Δ) :
    ∃ ε : (𝓞 F)ˣ, (mt γ).det = algebraMap F (Lsq F Δ) (algebraMap (𝓞 F) F ε) := by
  have h1 : ∀ v, (mt ((ι γ).1 v)).det * (mt (k.1 v)).det = 1 := fun v => by
    have h2 : (mt ((ι γ).1 v * (y.1 v * k.1 v * (y.1 v)⁻¹))).det = 1 := mem_SA.1 h v
    rwa [det_mul', det_mul', det_mul', mul_right_comm, det_inv', one_mul] at h2
  obtain ⟨a, ha⟩ := re_int hι γ fun v => by
    have h2 := det_int (inv_mem (mem_box.1 hk v))
    have h3 := det_inv' (k.1 v)
    have : (mt ((ι γ).1 v)).det = (mt (k.1 v)⁻¹).det := by
      rw [← mul_one (mt ((ι γ).1 v)).det, ← h3, ← mul_assoc, h1, one_mul]
    rwa [this]
  obtain ⟨b, hb⟩ := re_int hι γ⁻¹ fun v => by
    have h2 := det_int (mem_box.1 hk v)
    have h3 := det_inv' ((ι γ).1 v)
    have : (mt ((ι γ⁻¹).1 v)).det = (mt (k.1 v)).det := by
      rw [map_inv]
      change (mt ((ι γ).1 v)⁻¹).det = _
      rw [← one_mul (mt ((ι γ).1 v)⁻¹).det, ← h1, mul_right_comm, h3, one_mul]
    rwa [this]
  have hab : a * b = 1 := by
    apply IsFractionRing.injective (𝓞 F) F
    apply (algebraMap F (Lsq F Δ)).injective
    rw [map_mul, map_mul, ha, hb, ← det_im, ← det_im, det_inv', map_one, map_one]
  exact ⟨⟨a, b, hab, by rw [mul_comm, hab]⟩, by rw [det_im, ← ha]⟩

theorem finS_cls_of (D : Dat Δ) (ι : DX Δ →* DA Δ) (hι : IsIotaD ι)
    (hcls : ∃ Y : Finset (DA Δ), ∀ g, ∃ γ, ∃ y ∈ Y, ∃ k ∈ (rpg _ _).box (fun v : Pl F => KD (cv v Δ) (Ov v)), g = ι γ * y * k)
    (hU : D.U2.relIndex ((rpg _ _).box fun v : Pl F => KD (cv v Δ) (Ov v)) ≠ 0)
    {V : Type} [AddCommGroup V] [Module ℂ V] {ch : F → ℂ} {x : DA Δ} {B : Base (SU Δ) (SA Δ) V} (hB : D.IsBS ch x B) :
    ∃ S : Finset (SA Δ), ∀ g, ∃ γ, ∃ s ∈ S, ∃ u ∈ B.U, g = B.ι γ * s * u := by
  classical
  have : Group.FG (𝓞 F)ˣ := Group.fg_iff_monoid_fg.2 inferInstance
  have := Subgroup.finiteIndex_range_powMonoidHom_of_fg (𝓞 F)ˣ (n := 2) two_ne_zero
  have := SA_normal (Δ := Δ)
  let P : DX Δ → Prop := fun γ => ∃ ε : (𝓞 F)ˣ, (mt γ).det = algebraMap F (Lsq F Δ) (algebraMap (𝓞 F) F ε)
  let c : DX Δ → (𝓞 F)ˣ ⧸ (powMonoidHom 2 : (𝓞 F)ˣ →* (𝓞 F)ˣ).range := fun γ => if h : P γ then (h.choose : (𝓞 F)ˣ) else 1
  obtain ⟨S, hS⟩ := su_abs ι (SU Δ) (SA Δ) _ D.U2 (fun γ hγ => mem_SA.2 fun v => by rw [det_iota hι, mem_SU.1 hγ, map_one]) hU hcls x P c
    (unit_det hι) (by
      intro γ γ' h h' e
      simp only [c, dif_pos h, dif_pos h'] at e
      obtain ⟨η, hη⟩ := QuotientGroup.eq.1 e
      have hη' : h'.choose = h.choose * η ^ 2 := by rw [show η ^ 2 = _ from hη]; group
      let z := scal Δ (Units.map (algebraMap (𝓞 F) F : 𝓞 F →* F) η)
      have hz : ∀ v, mt ((ι z).1 v) = scalar (Fin 2) (algebraMap (Kv v) (Lsq (Kv v) (cv v Δ)) (cv v (algebraMap (𝓞 F) F η))) := by
        intro v
        rw [hι, mt_scal, ← lmap_alg]
        ext i j : 1
        fin_cases i <;> fin_cases j <;> simp
      refine ⟨z, mem_box.2 fun v => scal_KD (Units.map (algebraMap (𝓞 F) (Ov v) : 𝓞 F →* Ov v) η) _ ?_, ?_, ?_⟩
      · rw [hz]; rfl
      · refine Subgroup.mem_center_iff.2 fun g => Subtype.ext (funext fun v => Subtype.ext (Units.ext ?_))
        change mt (g.1 v) * mt ((ι z).1 v) = mt ((ι z).1 v) * mt (g.1 v)
        rw [hz]
        exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).symm.eq
      · have hd : (mt z).det = algebraMap F (Lsq F Δ) (algebraMap (𝓞 F) F η) ^ 2 := by
          rw [mt_scal, Matrix.scalar_apply, Matrix.det_diagonal]; simp
        have h3 : (mt γ').det = (mt γ).det * (mt z).det := by
          rw [h'.choose_spec, hη', hd]
          conv_rhs => rw [h.choose_spec]
          simp
        rw [mem_SU, det_mul', det_mul', h3]
        linear_combination ((mt z).det * (mt z⁻¹).det) * det_inv' γ + det_inv' z)
  refine ⟨S, fun g => ?_⟩
  obtain ⟨γ, hγ, s, hs, u, hu, e⟩ := hS g
  refine ⟨⟨γ, hγ⟩, s, hs, u, (hB.U u).2 hu, Subtype.ext ?_⟩
  have : (B.ι ⟨γ, hγ⟩ : DA Δ) = ι γ :=
    Subtype.ext (funext fun v => Subtype.ext (Units.ext ((hB.ι ⟨γ, hγ⟩ v).trans (hι γ v).symm)))
  rw [e, ← this]; rfl

end Global

end UpperTheory.V.Z.Sym.Glob
