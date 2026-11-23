import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.EqOneOfMemLev

namespace UpperTheory.V.Af.Tw

private theorem glue_ext {G H B : Type*} [CommGroup G] [CommGroup H] [CommGroup B] (hB : KStar.Choice.IsDiv B)
    (p : G →* H) (f : G →* B) (h : ∀ x, p x = 1 → f x = 1) : ∃ F : H →* B, ∀ x, F (p x) = f x := by
  classical
  obtain ⟨F, hF⟩ := hB.exists_extension p.range
    ((QuotientGroup.lift p.ker f (fun x hx => (MonoidHom.mem_ker).2 (h x ((MonoidHom.mem_ker).1 hx)))).comp
      (QuotientGroup.quotientKerEquivRange p).symm.toMonoidHom)
  refine ⟨F, fun x => (hF ⟨p x, x, rfl⟩).trans ?_⟩
  have hx : (QuotientGroup.quotientKerEquivRange p).symm ⟨p x, x, rfl⟩ = (x : G ⧸ p.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hx]
  rfl

private theorem glue_exp (n M l : ℕ) (hM : 0 < M) (hl : l.Prime) :
    ∃ e k : ℕ, e ≡ 1 [MOD n] ∧ 0 < k ∧ (n.Coprime l → k.Coprime l) ∧ M ∣ e * k := by
  by_cases hc : n.Coprime l
  · have hM0 : M ≠ 0 := hM.ne'
    have hco : n.Coprime (l ^ M.factorization l) := Nat.Coprime.pow_right _ hc
    obtain ⟨e, he1, he0⟩ := Nat.chineseRemainder hco 1 0
    refine ⟨e, M / l ^ M.factorization l, he1, Nat.ordCompl_pos l hM0,
      fun _ => (Nat.coprime_ordCompl hl hM0).symm, ?_⟩
    have hd : l ^ M.factorization l ∣ e := (Nat.modEq_zero_iff_dvd).1 he0
    calc M = l ^ M.factorization l * (M / l ^ M.factorization l) :=
          (Nat.ordProj_mul_ordCompl_eq_self M l).symm
      _ ∣ e * (M / l ^ M.factorization l) := mul_dvd_mul_right hd _
  · exact ⟨1, M, Nat.ModEq.refl 1, hM, fun h' => absurd h' hc, by simp⟩

theorem glue : Glue := by
  unfold Glue
  intro I J K B _ _ _ _ hB i d c σ U V N g n M l hM hl h1 h2 h3 h4 h5 h6 h7 h8
  obtain ⟨e, k, he, hk0, hkc, hMk⟩ := glue_exp n M l hM hl
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : J × K × U →* I, ∀ z, p₀ z = i z.1 * d z.2.1 * (z.2.2 : I) :=
    ⟨i.comp (MonoidHom.fst _ _) * d.comp ((MonoidHom.fst _ _).comp (MonoidHom.snd _ _)) *
      U.subtype.comp ((MonoidHom.snd _ _).comp (MonoidHom.snd _ _)), fun z => rfl⟩
  have hq : ∀ z, p₀ z = 1 → (z.2.2 : I) / c z.2.2 = d (σ z.2.1 / z.2.1) := by
    intro z hz
    rw [hp₀] at hz
    have hu : (z.2.2 : I) = (i z.1 * d z.2.1)⁻¹ := eq_inv_of_mul_eq_one_right hz
    rw [hu, map_inv, map_mul, h1, h2, map_div]
    simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  obtain ⟨pθ, hpθ⟩ : ∃ pθ : p₀.ker × V →* I,
      ∀ w, pθ w = d (σ (w.1 : J × K × U).2.1 / (w.1 : J × K × U).2.1) * (w.2 : I) :=
    ⟨d.comp ((σ / MonoidHom.id K).comp ((MonoidHom.fst _ _).comp ((MonoidHom.snd _ _).comp
      (p₀.ker.subtype.comp (MonoidHom.fst _ _))))) * V.subtype.comp (MonoidHom.snd _ _), fun w => rfl⟩
  obtain ⟨fθ, hfθ⟩ : ∃ fθ : p₀.ker × V →* B,
      ∀ w, fθ w = (N (w.1 : J × K × U).1 * g ((w.1 : J × K × U).2.2 : I))⁻¹ :=
    ⟨((N.comp (MonoidHom.fst _ _) * g.comp (U.subtype.comp ((MonoidHom.snd _ _).comp
      (MonoidHom.snd _ _)))).comp (p₀.ker.subtype.comp (MonoidHom.fst _ _)))⁻¹, fun w => rfl⟩
  obtain ⟨θ₁, hθ₁⟩ := glue_ext hB pθ fθ (by
    rintro ⟨⟨⟨a, x, u⟩, hz⟩, v⟩ hw
    rw [hpθ] at hw
    rw [hfθ]
    dsimp only at hw ⊢
    have hz' : p₀ (a, x, u) = 1 := MonoidHom.mem_ker.1 hz
    rw [hp₀] at hz'
    dsimp only at hz'
    have hv : d (σ x / x) = (v : I)⁻¹ := eq_inv_of_mul_eq_one_left hw
    have hσ : σ x = x := h7 x (by rw [hv]; exact inv_mem v.2)
    obtain ⟨a', ha', hN⟩ := h5 x hσ
    have hiu : i (a * a') = (u : I)⁻¹ := by
      rw [map_mul, ha']
      exact eq_inv_of_mul_eq_one_left hz'
    have h4' := h4 (a * a') (by rw [hiu]; exact inv_mem u.2)
    rw [hiu, map_inv, map_mul, hN, mul_one] at h4'
    rw [← h4', inv_mul_cancel, inv_one])
  obtain ⟨θ, hθ⟩ : ∃ θ : I →* B, ∀ y, θ y = θ₁ y ^ e := ⟨(powMonoidHom e).comp θ₁, fun y => rfl⟩
  have hV : ∀ v ∈ V, θ₁ v = 1 := by
    intro v hv
    have h := hθ₁ (1, ⟨v, hv⟩)
    rw [hpθ, hfθ] at h
    simpa using h
  have hZ : ∀ z, p₀ z = 1 → θ (z.2.2 / c z.2.2) = (N z.1 * g z.2.2)⁻¹ := by
    intro z hz
    have h := hθ₁ (⟨z, MonoidHom.mem_ker.2 hz⟩, 1)
    rw [hpθ, hfθ] at h
    dsimp only at h
    simp only [OneMemClass.coe_one, mul_one] at h
    rw [hθ, hq z hz, h]
    have hw : ((N z.1 * g z.2.2)⁻¹) ^ n = 1 := by
      have hmem : d (σ z.2.1 / z.2.1) ∈ U := by
        rw [← hq z hz]
        exact div_mem z.2.2.2 (h3 _ z.2.2.2)
      rw [← h, ← map_pow, ← map_pow, h6 _ hmem, map_one, map_one]
    rw [pow_eq_pow_mod e hw, show e % n = 1 % n from he, ← pow_eq_pow_mod 1 hw, pow_one]
  obtain ⟨f, hf⟩ : ∃ f : J × K × U →* B, ∀ z, f z = N z.1 * (g z.2.2 * θ (z.2.2 / c z.2.2)) :=
    ⟨N.comp (MonoidHom.fst _ _) * (g.comp (U.subtype.comp ((MonoidHom.snd _ _).comp
      (MonoidHom.snd _ _))) * θ.comp ((U.subtype / c.comp U.subtype).comp
      ((MonoidHom.snd _ _).comp (MonoidHom.snd _ _)))), fun z => rfl⟩
  obtain ⟨ψ, hψ⟩ := glue_ext hB p₀ f (by
    intro z hz
    rw [hf, hZ z hz, ← mul_assoc, mul_inv_cancel])
  refine ⟨ψ, θ, fun a => ?_, fun x => ?_, fun u hu => ?_, fun v hv => ?_, k, hk0, hkc, fun u hu => ?_⟩
  · have h := hψ (a, 1, 1)
    rw [hp₀, hf] at h
    simpa using h
  · have h := hψ (1, x, 1)
    rw [hp₀, hf] at h
    simpa using h
  · have h := hψ (1, 1, ⟨u, hu⟩)
    rw [hp₀, hf] at h
    simpa using h
  · rw [hθ, hV v hv, one_pow]
  · obtain ⟨j, hj⟩ := hMk
    rw [hθ, ← pow_mul, ← map_pow, hj, pow_mul]
    exact hV _ (pow_mem (h8 u hu) j)

end UpperTheory.V.Af.Tw
