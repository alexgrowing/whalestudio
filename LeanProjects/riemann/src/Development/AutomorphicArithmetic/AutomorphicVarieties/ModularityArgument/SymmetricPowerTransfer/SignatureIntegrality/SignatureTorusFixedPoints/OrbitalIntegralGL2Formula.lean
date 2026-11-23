import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ScalarComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Contract
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ConjDiag
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem scal_eq (z : kˣ) : GeneralLinearGroup.scalar (Fin 2) z = dg (fun _ : Fin 2 => z) := by
  ext i j
  simp [dg, val_diagT, Matrix.diagonal_apply, Matrix.one_apply, GeneralLinearGroup.scalar]

private theorem scal_comm (z : kˣ) (g : GL (Fin 2) k) :
    GeneralLinearGroup.scalar (Fin 2) z * g = g * GeneralLinearGroup.scalar (Fin 2) z := by
  ext : 1
  simp only [Units.val_mul]
  exact (Matrix.scalar_commute (n := Fin 2) (z : k) (fun _ => Commute.all _ _) (g : Matrix (Fin 2) (Fin 2) k))

private theorem sdom2 {x y : kˣ} (h : valuation k (x : k) < valuation k (y : k)) : SDom ![x, y] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

private theorem key (V : Lev k) {d : Fin 2 → kˣ} (hd : SDom d) {a b z : kˣ}
    (hab : valuation k (a : k) < valuation k (b : k)) {w : GL (Fin 2) k}
    (h : (GeneralLinearGroup.scalar (Fin 2) z)⁻¹ * (w⁻¹ * dg ![a, b] * w) ∈ V.DC d) :
    ∃ (u : Fin 2 → kˣ), ∃ j ∈ V.J 2, w = dg u * j ∧ a / (z * d 0) ∈ V.H ∧ b / (z * d 1) ∈ V.H := by
  obtain ⟨j, hj, s, hs, E⟩ := contract k V 2 (MonoidHom.id _) (pres_id V 2) d hd _ h
  obtain ⟨s', hs', rfl⟩ := Subgroup.mem_map.mp hs
  simp only [Subgroup.mem_pi, Set.mem_univ, true_implies] at hs'
  have hv : ∀ i, valuation k ((s' i : kˣ) : k) = 1 := fun i => V.H_le (hs' i)
  have hE : (w * j)⁻¹ * dg ![a, b] * (w * j) = dg (fun i => z * s' i * d i) := by
    have c := scal_comm z j⁻¹
    calc (w * j)⁻¹ * dg ![a, b] * (w * j)
        = GeneralLinearGroup.scalar (Fin 2) z * (j⁻¹ * ((GeneralLinearGroup.scalar (Fin 2) z)⁻¹ *
            (w⁻¹ * dg ![a, b] * w)) * MonoidHom.id _ j) := by
          simp only [MonoidHom.id_apply, ← mul_assoc]
          rw [c]
          group
      _ = dg (fun i => z * s' i * d i) := by
          rw [E, scal_eq]
          simp only [dg, ← map_mul]
          congr 1
          funext i
          simp [mul_assoc]
  have hsd : SDom (fun i => z * s' i * d i) := by
    intro i i' hii
    simp only [Units.val_mul, map_mul, hv, mul_one]
    have hz0 : valuation k (z : k) ≠ 0 := by simp
    exact mul_lt_mul_of_pos_left (hd i i' hii) (zero_lt_iff.mpr hz0)
  obtain ⟨hab', u, hu⟩ := conjDiag k 2 ![a, b] _ (sdom2 hab) hsd (w * j) hE
  refine ⟨u, j⁻¹, inv_mem hj, ?_, ?_, ?_⟩
  · rw [← hu]
    group
  · have h0 : a = z * s' 0 * d 0 := congrFun hab' 0
    rw [h0, mul_right_comm, mul_div_cancel_left]
    exact hs' 0
  · have h1 : b = z * s' 1 * d 1 := congrFun hab' 1
    rw [h1, mul_right_comm, mul_div_cancel_left]
    exact hs' 1

private theorem orbit_of {T : Type} [Group T] (V : Lev k) {p q : T →* kˣ}
    (hpq : ∀ x : kˣ, ∃ t, p t / q t = x) {g₀ : GL (Fin 2) k} {ι : T →* GL (Fin 2) k}
    (hι : ∀ s, ι s = g₀ * dg ![p s, q s] * g₀⁻¹) {u : Fin 2 → kˣ} {j : GL (Fin 2) k} (hj : j ∈ V.J 2) :
    ∃ t, ∃ v ∈ V.ZJ 2, g₀ * (dg u * j) = ι t * g₀ * v := by
  obtain ⟨t, ht⟩ := hpq (u 0 / u 1)
  have hz : GeneralLinearGroup.scalar (Fin 2) (u 1 / q t) ∈ V.ZJ 2 := by
    show _ ∈ (GeneralLinearGroup.scalar (Fin 2)).range ⊔ V.J 2
    exact Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hzj : GeneralLinearGroup.scalar (Fin 2) (u 1 / q t) * j ∈ V.ZJ 2 := by
    refine mul_mem hz ?_
    show _ ∈ (GeneralLinearGroup.scalar (Fin 2)).range ⊔ V.J 2
    exact Subgroup.mem_sup_right hj
  refine ⟨t, _, hzj, ?_⟩
  have h0 : u 0 = p t / q t * u 1 := by rw [ht, div_mul_cancel]
  have hu : u = ![p t, q t] * fun _ => u 1 / q t := by
    funext i
    fin_cases i
    · show u 0 = p t * (u 1 / q t)
      rw [h0, mul_div_assoc', div_mul_eq_mul_div]
    · show u 1 = q t * (u 1 / q t)
      rw [mul_div_cancel]
  rw [hι, scal_eq]
  conv_lhs => rw [hu]
  simp only [dg, map_mul]
  group

private theorem orb_congr' {T G : Type} [Group T] [Group G] (ι : T →* G) (C : Subgroup T) (θ : G →* G) (U : Subgroup G)
    {f f' : G → ℂ} (δ : G) (h : ∀ y, f (y⁻¹ * δ * θ y) = f' (y⁻¹ * δ * θ y)) :
    orb ι C θ U f δ = orb ι C θ U f' δ := by
  simp only [orb, h]

private theorem orb_smul' {T G : Type} [Group T] [Group G] (ι : T →* G) (C : Subgroup T) (θ : G →* G) (U : Subgroup G)
    (c : ℂ) (f : G → ℂ) (δ : G) :
    orb ι C θ U (fun g => c * f g) δ = c * orb ι C θ U f δ := by
  unfold orb wcount
  simp only [mul_left_comm _ c]
  exact (smul_finsum c _).symm

private theorem orb_zero' {T G : Type} [Group T] [Group G] (ι : T →* G) (C : Subgroup T) (θ : G →* G) (U : Subgroup G)
    (δ : G) : orb ι C θ U (fun _ => 0) δ = 0 := by
  simp [orb, wcount]

private theorem inv_gt {x : kˣ} (h : valuation k (x : k) < 1) : valuation k (x : k) < valuation k ((x⁻¹ : kˣ) : k) := by
  have hp : 0 < valuation k (x : k) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 x.ne_zero)
  rw [Units.val_inv_eq_inv_val, map_inv₀]
  exact h.trans ((one_lt_inv₀ hp).2 h)

private theorem key' (V : Lev k) {d : Fin 2 → kˣ} (hd : SDom d) {a b z : kˣ}
    (hab : valuation k (a : k) < valuation k (b : k)) (g₀ y : GL (Fin 2) k)
    (h : (GeneralLinearGroup.scalar (Fin 2) z)⁻¹ * (y⁻¹ * (g₀ * dg ![a, b] * g₀⁻¹) * MonoidHom.id _ y) ∈ V.DC d) :
    ∃ (u : Fin 2 → kˣ), ∃ j ∈ V.J 2, y = g₀ * (dg u * j) ∧ a / (z * d 0) ∈ V.H ∧ b / (z * d 1) ∈ V.H := by
  have e : (g₀⁻¹ * y)⁻¹ * dg ![a, b] * (g₀⁻¹ * y) = y⁻¹ * (g₀ * dg ![a, b] * g₀⁻¹) * MonoidHom.id _ y := by
    simp only [MonoidHom.id_apply]; group
  obtain ⟨u, j, hj, hw, h1, h2⟩ := key V hd hab (w := g₀⁻¹ * y) (z := z) (by rw [e]; exact h)
  exact ⟨u, j, hj, by rw [← hw]; group, h1, h2⟩

private theorem fin_of {T : Type} [Group T] (V : Lev k) {d : Fin 2 → kˣ} (hd : SDom d) {a b : kˣ}
    (hab : valuation k (a : k) < valuation k (b : k)) {p q : T →* kˣ}
    (hpq : ∀ x : kˣ, ∃ t, p t / q t = x) {g₀ : GL (Fin 2) k} {ι : T →* GL (Fin 2) k}
    (hι : ∀ s, ι s = g₀ * dg ![p s, q s] * g₀⁻¹) (f : GL (Fin 2) k → ℂ)
    (hf : ∀ g, f g ≠ 0 → ∃ z : kˣ, (GeneralLinearGroup.scalar (Fin 2) z)⁻¹ * g ∈ V.DC d) :
    FinOrb ι (MonoidHom.id _) (V.ZJ 2) f (g₀ * dg ![a, b] * g₀⁻¹) := by
  refine ⟨{g₀}, fun y hy => ?_⟩
  obtain ⟨z, hz⟩ := hf _ hy
  obtain ⟨u, j, hj, rfl, -, -⟩ := key' V hd hab g₀ y hz
  obtain ⟨t, v, hv, e⟩ := orbit_of V hpq hι (u := u) hj
  exact ⟨t, g₀, by simp, v, hv, e⟩

end

theorem UpperTheory.V.Z.Sym.Sig.orbital_integral_degree_one : UpperTheory.V.Z.Sym.Sig.OrbitalIntegralGL2Formula := by
  intro k _ _ _ _ V χ hχ t ht T _ p q hpq g₀ ι hι a ha
  have hpq' : ∀ x : kˣ, ∃ s, p s / q s = x := fun x => by
    obtain ⟨s, hs⟩ := hpq x
    exact ⟨s, by simpa using hs⟩
  have htd : SDom ![t, t⁻¹] := sdom2 (inv_gt ht)
  have haa : valuation k (a : k) < valuation k ((a⁻¹ : kˣ) : k) := inv_gt ha
  have ht1 : SDom ![t, 1] := sdom2 (by simpa using ht)
  refine ⟨⟨?_, ?_⟩, fun b hb => ?_⟩
  · refine fin_of V htd haa hpq' hι (V.quaternionDoubleCosetIndicator t) (fun g hg => ⟨1, ?_⟩)
    have hm : g ∈ V.DC ![t, t⁻¹] := by
      by_contra hn
      exact hg (by simp [Lev.quaternionDoubleCosetIndicator, Glob.one, hn])
    simpa using hm
  · have h1H : ∀ u ∈ V.H, (1 : kˣ →* ℂˣ) u = 1 := fun _ _ => rfl
    have E := (orbZ k V 1 h1H ![t, t⁻¹] htd T p q hpq g₀ ι hι a a⁻¹ haa).2
    by_cases hat : a / t ∈ V.H
    · have hX : ∀ y : GL (Fin 2) k,
          V.quaternionDoubleCosetIndicator t (y⁻¹ * (g₀ * dg ![a, a⁻¹] * g₀⁻¹) * MonoidHom.id _ y) =
          V.fZ 1 ![t, t⁻¹] (y⁻¹ * (g₀ * dg ![a, a⁻¹] * g₀⁻¹) * MonoidHom.id _ y) := by
        intro y
        have hiff : y⁻¹ * (g₀ * dg ![a, a⁻¹] * g₀⁻¹) * MonoidHom.id _ y ∈ V.DC ![t, t⁻¹] ↔
            ∃ z : kˣ, (GeneralLinearGroup.scalar (Fin 2) z)⁻¹ *
              (y⁻¹ * (g₀ * dg ![a, a⁻¹] * g₀⁻¹) * MonoidHom.id _ y) ∈ V.DC ![t, t⁻¹] := by
          constructor
          · intro hm
            exact ⟨1, by simpa using hm⟩
          · rintro ⟨z, hz⟩
            obtain ⟨u, j, hj, rfl, -, -⟩ := key' V htd haa g₀ y hz
            have hr : dg ![a / t, (a / t)⁻¹] ∈ V.J 2 := by
              have hm : dg ![a / t, (a / t)⁻¹] ∈ V.TH 2 := by
                refine Subgroup.mem_map_of_mem _ ?_
                simp only [Subgroup.mem_pi, Set.mem_univ, true_implies]
                intro i
                fin_cases i
                · exact hat
                · exact inv_mem hat
              show _ ∈ (glIwa k 2).N ⊔ V.TH 2 ⊔ (glIwa k 2).Nm V.c
              exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hm)
            refine ⟨j⁻¹, inv_mem hj, dg ![a / t, (a / t)⁻¹] * j, mul_mem hr hj, ?_⟩
            have hD : dg ![a, a⁻¹] = dg u * (dg ![t, t⁻¹] * dg ![a / t, (a / t)⁻¹]) * (dg u)⁻¹ := by
              simp only [dg, ← map_mul, ← map_inv]
              congr 1
              funext i
              fin_cases i
              · show a = u 0 * (t * (a / t)) * (u 0)⁻¹
                rw [mul_div_cancel, mul_inv_cancel_comm]
              · show a⁻¹ = u 1 * (t⁻¹ * (a / t)⁻¹) * (u 1)⁻¹
                rw [← mul_inv, mul_div_cancel, mul_inv_cancel_comm]
            rw [hD]
            simp only [MonoidHom.id_apply]
            group
        by_cases hm : y⁻¹ * (g₀ * dg ![a, a⁻¹] * g₀⁻¹) * MonoidHom.id _ y ∈ V.DC ![t, t⁻¹]
        · simp only [Lev.quaternionDoubleCosetIndicator, Lev.fZ, Glob.one]
          rw [if_pos hm, dif_pos (hiff.mp hm)]
          simp
        · simp only [Lev.quaternionDoubleCosetIndicator, Lev.fZ, Glob.one]
          rw [if_neg hm, dif_neg (mt hiff.mpr hm)]
      rw [orb_congr' ι _ _ _ _ hX, E]
      have hsq : a / a⁻¹ / (![t, t⁻¹] 0 / ![t, t⁻¹] 1) = (a / t) * (a / t) := by
        ext
        simp [Units.val_div_eq_div_val]
        field_simp
      rw [hsq, if_pos (mul_mem hat hat)]
      simp [Glob.one, hat]
    · have hX : ∀ y : GL (Fin 2) k,
          V.quaternionDoubleCosetIndicator t (y⁻¹ * (g₀ * dg ![a, a⁻¹] * g₀⁻¹) * MonoidHom.id _ y) =
          (fun _ => (0 : ℂ)) (y⁻¹ * (g₀ * dg ![a, a⁻¹] * g₀⁻¹) * MonoidHom.id _ y) := by
        intro y
        simp only [Lev.quaternionDoubleCosetIndicator, Glob.one]
        rw [if_neg]
        intro hm
        have hz : (GeneralLinearGroup.scalar (Fin 2) (1 : kˣ))⁻¹ *
            (y⁻¹ * (g₀ * dg ![a, a⁻¹] * g₀⁻¹) * MonoidHom.id _ y) ∈ V.DC ![t, t⁻¹] := by
          simpa using hm
        obtain ⟨u, j, hj, -, h0, -⟩ := key' V htd haa g₀ y hz
        apply hat
        simpa using h0
      rw [orb_congr' (f' := fun _ => (0 : ℂ)) ι _ _ _ _ hX, orb_zero']
      simp [Glob.one, hat]
  have h1a : 1 < valuation k ((a⁻¹ : kˣ) : k) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    exact (one_lt_inv₀ (zero_lt_iff.mpr (by simp))).mpr ha
  have hvb : valuation k (b : k) = valuation k ((a⁻¹ : kˣ) : k) := by
    rw [hb]
    exact Valuation.map_add_eq_of_lt_right _ (by simpa using h1a)
  have habb : valuation k ((a * b : kˣ) : k) < valuation k (b : k) := by
    rw [Units.val_mul, map_mul]
    exact mul_lt_of_lt_one_left (zero_lt_iff.mpr (by simp)) ha
  refine ⟨?_, ?_⟩
  · refine fin_of V ht1 habb hpq' hι (V.twistedCentralTestFunction χ t) (fun g hg => ?_)
    by_contra hn
    apply hg
    simp only [Lev.twistedCentralTestFunction, Lev.fZ]
    rw [dif_neg hn, mul_zero]
  · have hχH : ∀ u ∈ V.H, χ u = 1 := fun u hu => hχ u (V.H_le hu)
    have E := (orbZ k V χ hχH ![t, 1] ht1 T p q hpq g₀ ι hι (a * b) b habb).2
    have hfk : V.twistedCentralTestFunction χ t = fun g => (((χ t)⁻¹ : ℂˣ) : ℂ) * V.fZ χ ![t, 1] g := rfl
    rw [hfk, orb_smul', E]
    have hq : a * b / b / (![t, 1] 0 / ![t, 1] 1) = a / t := by simp
    rw [hq]
    by_cases hat : a / t ∈ V.H
    · rw [if_pos hat]
      have hvat : valuation k (a : k) = valuation k (t : k) := by
        have h1 : valuation k ((a / t : kˣ) : k) = 1 := V.H_le hat
        rw [Units.val_div_eq_div_val, map_div₀, div_eq_one_iff_eq (by simp)] at h1
        exact h1
      have htb : t * b ∈ Uo k := by
        show valuation k ((t * b : kˣ) : k) = 1
        rw [Units.val_mul, map_mul, hvb, ← hvat, Units.val_inv_eq_inv_val, map_inv₀,
          mul_inv_cancel₀ (by simp)]
      have hc : (χ t)⁻¹ * χ (![t, 1] 1 / b) = 1 := by
        have := hχ _ htb
        simp only [map_mul] at this
        show (χ t)⁻¹ * χ (1 / b) = 1
        rw [one_div, map_inv, ← mul_inv, this, inv_one]
      simp only [Glob.one, if_pos hat]
      rw [mul_left_comm, ← Units.val_mul, hc, Units.val_one]
    · simp [Glob.one, hat]

end
