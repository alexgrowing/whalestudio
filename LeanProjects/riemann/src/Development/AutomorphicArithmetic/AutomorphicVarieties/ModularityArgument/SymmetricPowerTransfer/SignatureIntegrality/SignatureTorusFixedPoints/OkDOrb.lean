import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.IsIntegralLf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.OrbMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ModelD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.OrbitalIntegralGL2Formula
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.OkS
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.OkKValLt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.IsIntegralOfEv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.StabFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ScMemIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FinFacts

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Z.Sym.Sig

open Loc Glob

private theorem scalar_comm {k : Type} [Field k] (z : kˣ) (g : GL (Fin 2) k) :
    GeneralLinearGroup.scalar (Fin 2) z * g = g * GeneralLinearGroup.scalar (Fin 2) z := by
  apply Units.ext
  simp only [GeneralLinearGroup.scalar, Units.val_mul]
  ext i j
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

private theorem conj_scalar {k : Type} [Field k] (c : kˣ) (w x : GL (Fin 2) k) :
    (GeneralLinearGroup.scalar (Fin 2) c * w)⁻¹ * x * (GeneralLinearGroup.scalar (Fin 2) c * w) = w⁻¹ * x * w := by
  have e := scalar_comm c x
  generalize GeneralLinearGroup.scalar (Fin 2) c = C at e ⊢
  calc (C * w)⁻¹ * x * (C * w) = w⁻¹ * C⁻¹ * (x * C) * w := by group
    _ = w⁻¹ * x * w := by rw [← e]; group

private theorem mt_conj {K : Type} [Field K] {Δ : K} (y g : DX Δ) :
    (mt (y⁻¹ * g * y)).trace = (mt g).trace ∧ (mt (y⁻¹ * g * y)).det = (mt g).det := by
  have e : mt (y⁻¹ * g * y) = mt y⁻¹ * (mt g * mt y) := by
    rw [← Matrix.mul_assoc]; rfl
  have e2 : mt y * mt y⁻¹ = 1 := by
    change mt (y * y⁻¹) = 1
    rw [mul_inv_cancel]; rfl
  constructor
  · rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, e2, Matrix.mul_one]
  · have e3 := congrArg Matrix.det e2
    rw [Matrix.det_mul, Matrix.det_one] at e3
    rw [e, Matrix.det_mul, Matrix.det_mul]
    linear_combination (mt g).det * e3

private theorem emb_comm {K : Type} [Field K] {Δ τ : K} {γ : DX Δ} {j : (Etau K τ)ˣ →* DX Δ}
    (h : IsEmb τ γ j) (u : (Etau K τ)ˣ) : (j u)⁻¹ * γ * j u = γ := by
  have e : j u * γ = γ * j u := by
    apply Subtype.ext
    apply Units.ext
    change mt (j u) * mt γ = mt γ * mt (j u)
    rw [h u]
    simp [add_mul, mul_add]
  rw [mul_assoc, ← e]
  group

private theorem re_im {K : Type} [Field K] {τ : K} {z : (Etau K τ)ˣ}
    (hz : (z : Etau K τ) = 1 + QuadraticAlgebra.omega) :
    (z : Etau K τ).re = 1 ∧ (z : Etau K τ).im = 1 := by
  rw [hz]
  simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private theorem jz_facts {K : Type} [Field K] {Δ τ : K} {γ : DX Δ} {j : (Etau K τ)ˣ →* DX Δ}
    (hT : HasTr γ τ) (h : IsEmb τ γ j) {z : (Etau K τ)ˣ} (hz : (z : Etau K τ) = 1 + QuadraticAlgebra.omega) :
    (mt (j z)).trace = algebraMap K _ (2 + τ) ∧ (mt (j z)).det = algebraMap K _ (2 + τ) := by
  obtain ⟨h1, h2⟩ := re_im hz
  have e : mt (j z) = 1 + mt γ := by
    rw [h z, h1, h2, one_smul, one_smul]
  obtain ⟨hd, ht⟩ := hT
  rw [Matrix.det_fin_two] at hd
  rw [Matrix.trace_fin_two] at ht
  rw [e, map_add, map_ofNat]
  constructor
  · rw [Matrix.trace_fin_two]
    simp only [Matrix.add_apply, Matrix.one_apply_eq]
    linear_combination ht
  · rw [Matrix.det_fin_two]
    simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
    linear_combination hd + ht

private theorem two_add_ne {K : Type} [Field K] {Δ τ : K} {γ : DX Δ} {j : (Etau K τ)ˣ →* DX Δ}
    (hT : HasTr γ τ) (h : IsEmb τ γ j) {z : (Etau K τ)ˣ} (hz : (z : Etau K τ) = 1 + QuadraticAlgebra.omega) :
    2 + τ ≠ 0 := by
  intro h0
  have hu : IsUnit (mt (j z)).det := (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
  rw [(jz_facts hT h hz).2, h0, map_zero] at hu
  exact not_isUnit_zero hu

private theorem dg_scalar {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (c : kˣ) (d : Fin 2 → kˣ) : dg (fun i => c * d i) = GeneralLinearGroup.scalar (Fin 2) c * dg d := by
  have e : ((GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = diagonal fun _ => (c : k) := by
    simp [GeneralLinearGroup.scalar]
  apply Units.ext
  rw [Units.val_mul, e, dg, dg, val_diagT, val_diagT, Matrix.diagonal_mul_diagonal]
  simp

private theorem move_central {G : Type} [Group G] (C g D W : G) (hc : ∀ x, C * x = x * C) :
    W⁻¹ * (g * (C * D) * g⁻¹ * W) = C * ((g⁻¹ * W)⁻¹ * D * (g⁻¹ * W)) := by
  have e5 : g * (C * D) = C * (g * D) := by rw [← mul_assoc, ← hc g, mul_assoc]
  have e6 : W⁻¹ * C = C * W⁻¹ := (hc _).symm
  calc W⁻¹ * (g * (C * D) * g⁻¹ * W) = (W⁻¹ * C) * (g * D * g⁻¹ * W) := by rw [e5]; group
    _ = _ := by rw [e6]; group

private theorem evU_val {K : Type} [Field K] {τ a : K} (h : a * a = τ * a - 1) (z : (Etau K τ)ˣ) :
    ((evU h z : Kˣ) : K) = (z : Etau K τ).re + a * (z : Etau K τ).im := rfl

private theorem quot_pow_zero {R : Type} [CommRing R] (I : Ideal R) : Subsingleton (R ⧸ I ^ 0) :=
  Ideal.Quotient.subsingleton_iff.2 (by rw [pow_zero, Ideal.one_eq_top])

private theorem uc_relIndex (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) :
    (Uc k m).relIndex (Uo k) ≠ 0 := by
  cases m with
  | succ c => exact (finFacts k (Lev.deep k c)).1
  | zero =>
    refine fun h => (finFacts k (Lev.deep k 0)).1 (Subgroup.relIndex_eq_zero_of_le_left (H := Uc k (0 + 1)) ?_ h)
    refine Subgroup.map_mono fun u _ => ?_
    rw [MonoidHom.mem_ker]
    apply Units.ext
    exact (quot_pow_zero _).elim _ _

private theorem diagonal_orbit_admissible : OkDOrb := by
  intro k _ _ _ _ O _ _ hO h2 Δ s hs hs0 V Ry hRy χ hχ t ht S τ γ j hτ hTr hE z hz
  obtain ⟨hbij, -, -, -, -, hZJ⟩ := eD_facts k O hO h2 Δ s hs hs0
  have hZ : ZD Δ ⊔ S.J2 = (V.ZJ 2).comap (eD hs) := (hZJ V).symm
  suffices key : ∀ U : Subgroup (DX Δ), U = (V.ZJ 2).comap (eD hs) →
      (FinOrb j (MonoidHom.id _) U (S.fS t) γ ∧ FinOrb j (MonoidHom.id _) U (S.fK t) (j z) ∧
      orb j (Cint O τ) (MonoidHom.id _) U (S.fS t) γ = S.cS * UpperTheory.V.Z.Sym.Glob.one (Ind S.H τ t) ∧
      orb j (Cint O τ) (MonoidHom.id _) U (S.fK t) (j z) = S.cK * UpperTheory.V.Z.Sym.Glob.one (Ind S.H τ t) ∧
      (Ind S.H τ t → ∀ y : DX Δ ⧸ U, ((MulAction.stabilizer (DX Δ) y).comap j).relIndex (Cint O τ) ≠ 0)) from key _ hZ
  intro U hU
  subst hU
  have ht' : valuation k (t : k) < valuation k (unif k : k) ^ 2 := ht
  have hu1 : valuation k (unif k : k) < 1 := by
    rw [GlAx.unif_spec]; exact uniformizer_lt_one
  have ht1 : valuation k (t : k) < 1 := ht'.trans_le (pow_le_one₀ zero_le hu1.le)
  by_cases hI : Ind S.H τ t
  · have hI' := hI
    obtain ⟨h, hh, rfl⟩ := hI'
    have hh' : h ∈ V.H := hh
    have ha : valuation k ((t * h : kˣ) : k) < 1 := by
      have h1 : valuation k (h : k) = 1 := V.H_le hh'
      rw [Units.val_mul, map_mul, h1, mul_one]
      exact ht1
    obtain ⟨g₀, hγ, hj⟩ := modelD k O hO h2 Δ s hs hs0 (t * h) ha γ j hTr hE
    obtain ⟨hsurj, hC, -⟩ := roots k O hO (t * h) ha
    have hχ' : ∀ u ∈ V.H, χ u = 1 := fun u hu => hχ u (V.H_le hu)
    obtain ⟨-, hmem, hd⟩ := eqZ k V χ hχ' 2 (by norm_num)
    have hSD : SDom ![t, 1] := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> first | exact absurd hab (by decide) | simpa using ht1
    obtain ⟨-, -, hinvZ, -⟩ := hd ![t, 1] hSD
    have hinvS : ∀ u ∈ V.ZJ 2, ∀ x, V.quaternionDoubleCosetIndicator t (u⁻¹ * x * (MonoidHom.id _) u) = V.quaternionDoubleCosetIndicator t x := by
      intro u hu x
      obtain ⟨c, w, hw, rfl⟩ := (hmem u).1 hu
      rw [MonoidHom.id_apply, conj_scalar]
      have e : w⁻¹ * x * w ∈ V.DC ![t, t⁻¹] ↔ x ∈ V.DC ![t, t⁻¹] := by
        constructor
        · rintro ⟨p, hp, q, hq, e⟩
          refine ⟨w * p, mul_mem hw hp, q * w⁻¹, mul_mem hq (inv_mem hw), ?_⟩
          calc x = w * (w⁻¹ * x * w) * w⁻¹ := by group
            _ = _ := by rw [e]; group
        · rintro ⟨p, hp, q, hq, rfl⟩
          exact ⟨w⁻¹ * p, mul_mem (inv_mem hw) hp, q * w, mul_mem hq hw, by group⟩
      rw [Lev.quaternionDoubleCosetIndicator, Lev.quaternionDoubleCosetIndicator, propext e]
    have hinvK : ∀ u ∈ V.ZJ 2, ∀ x, V.twistedCentralTestFunction χ t (u⁻¹ * x * (MonoidHom.id _) u) = V.twistedCentralTestFunction χ t x := by
      intro u hu x
      obtain ⟨c, w, hw, rfl⟩ := (hmem u).1 hu
      rw [MonoidHom.id_apply, conj_scalar, Lev.twistedCentralTestFunction, Lev.twistedCentralTestFunction, hinvZ _ (inv_mem hw) _ hw x]
    have hcommK : ∀ u, (j u)⁻¹ * j z * (MonoidHom.id _) (j u) = j z := fun u => by
      rw [MonoidHom.id_apply, ← map_inv, ← map_mul, ← map_mul, mul_comm u⁻¹ z, inv_mul_cancel_right]
    obtain ⟨hoS, hfS, hst⟩ := orbMap _ _ _ (eD hs) hbij j (Cint O _) (MonoidHom.id _) (MonoidHom.id _) (fun _ => rfl)
      (V.ZJ 2) (V.quaternionDoubleCosetIndicator t) γ hinvS (emb_comm hE) inferInstance
    obtain ⟨hoK, hfK, -⟩ := orbMap _ _ _ (eD hs) hbij j (Cint O _) (MonoidHom.id _) (MonoidHom.id _) (fun _ => rfl)
      (V.ZJ 2) (V.twistedCentralTestFunction χ t) (j z) hinvK hcommK inferInstance
    obtain ⟨⟨hFS, hOS⟩, hK⟩ := orbital_integral_degree_one k V χ hχ t ht1 _ (evU (root_left (t * h))) (evU (root_right (t * h))) hsurj g₀
      ((eD hs).comp j) hj (t * h) ha
    obtain ⟨hre, him⟩ := re_im hz
    have hb : ((evU (root_right (t * h)) z : kˣ) : k) = 1 + ((t * h)⁻¹ : kˣ) := by
      rw [evU_val, hre, him, mul_one]
    have hzL : evU (root_left (t * h)) z = (t * h) * evU (root_right (t * h)) z := by
      apply Units.ext
      rw [Units.val_mul (t * h) _, hb, evU_val, hre, him, mul_one, mul_add, mul_one, Units.mul_inv, add_comm]
    obtain ⟨hFK, hOK⟩ := hK _ hb
    have hjz := hj z
    rw [hzL] at hjz
    rw [← hjz] at hFK hOK
    rw [← hγ] at hFS hOS
    have e1 : t * h / t ∈ V.H := by
      rw [mul_div_cancel_left]; exact hh'
    have f1 : UpperTheory.V.Z.Sym.Glob.one (t * h / t ∈ V.H) = 1 := if_pos e1
    have f2 : UpperTheory.V.Z.Sym.Glob.one (Ind S.H ((t * h : kˣ) + ((t * h)⁻¹ : kˣ) : k) t) = 1 := if_pos hI
    refine ⟨hfS.2 hFS, hfK.2 hFK, hoS.trans ?_, hoK.trans ?_, fun _ w => ?_⟩
    · rw [hC, hOS, f1, f2]
      simp [S, Lev.data]
    · rw [hC, hOK, f1, f2]
      simp [S, Lev.data]
    · obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
      have e := hst w
      change ((MulAction.stabilizer (DX Δ) (w : DX Δ ⧸ (V.ZJ 2).comap (eD hs))).comap j).relIndex _ ≠ 0
      rw [e, hC]
      obtain ⟨n, hn⟩ := stabFin k V 2 (g₀⁻¹ * eD hs w)
      set r := evU (root_left (t * h)) / evU (root_right (t * h)) with hr
      have hle : (Uc k n).comap r ≤
          (MulAction.stabilizer (GL (Fin 2) k) (eD hs w : GL (Fin 2) k ⧸ V.ZJ 2)).comap ((eD hs).comp j) := by
        intro u hu
        have hu' : r u ∈ Uc k n := hu
        have h3 := hn ![r u, 1] (by
          intro i
          fin_cases i
          · exact hu'
          · exact one_mem _)
        have ed : dg ![evU (root_left (t * h)) u, evU (root_right (t * h)) u] =
            GeneralLinearGroup.scalar (Fin 2) (evU (root_right (t * h)) u) * dg ![r u, 1] := by
          rw [← dg_scalar]
          congr 1
          funext i
          fin_cases i
          · simp [hr]
          · simp
        rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, MulAction.Quotient.smul_mk, eq_comm, QuotientGroup.eq,
          MonoidHom.comp_apply, hj, smul_eq_mul, ed]
        rw [move_central _ _ _ _ (scalar_comm _)]
        exact Subgroup.mul_mem_sup ⟨_, rfl⟩ h3
      refine fun h0 => uc_relIndex k n ?_
      have h1 := Subgroup.relIndex_eq_zero_of_le_left hle h0
      rwa [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hsurj] at h1
  · have hzS : ∀ y : DX Δ, S.fS t (y⁻¹ * γ * (MonoidHom.id _) y) = 0 := fun y => by
      by_contra hne
      refine hI ((okS k O hO h2 Δ s hs hs0 V Ry hRy χ hχ t ht).2.2 _ τ ?_ hne)
      refine ⟨?_, ?_⟩
      · rw [MonoidHom.id_apply, (mt_conj y γ).2]; exact hTr.1
      · rw [MonoidHom.id_apply, (mt_conj y γ).1]; exact hTr.2
    have hzK : ∀ y : DX Δ, S.fK t (y⁻¹ * j z * (MonoidHom.id _) y) = 0 := fun y => by
      by_contra hne
      obtain ⟨τ', hI', he⟩ := (okK k O hO h2 Δ s hs hs0 V Ry hRy χ hχ t ht).2.2 _ hne
      rw [MonoidHom.id_apply, (mt_conj y (j z)).1, (mt_conj y (j z)).2, (jz_facts hTr hE hz).1, (jz_facts hTr hE hz).2,
        ← map_pow, ← map_mul] at he
      have he' := (algebraMap k (Lsq k Δ)).injective he
      have hne2 := two_add_ne hTr hE hz
      have e : τ = τ' := by
        have : (2 + τ) * (τ - τ') = 0 := by linear_combination he'
        exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hne2)
      exact hI (e ▸ hI')
    refine ⟨?_, ?_, ?_, ?_, fun h => absurd h hI⟩
    · exact ⟨∅, fun y hy => absurd (hzS y) hy⟩
    · exact ⟨∅, fun y hy => absurd (hzK y) hy⟩
    · have e0 : UpperTheory.V.Z.Sym.Glob.one (Ind S.H τ t) = 0 := if_neg hI
      rw [e0, mul_zero]
      have hzS' : ∀ y : DX Δ, S.fS t (y⁻¹ * γ * y) = 0 := hzS
      simp [orb, wcount, hzS']
    · have e0 : UpperTheory.V.Z.Sym.Glob.one (Ind S.H τ t) = 0 := if_neg hI
      rw [e0, mul_zero]
      have hzK' : ∀ y : DX Δ, S.fK t (y⁻¹ * j z * y) = 0 := hzK
      simp [orb, wcount, hzK']

end UpperTheory.V.Z.Sym.Sig

theorem UpperTheory.V.Z.Sym.Sig.okDOrb :
    UpperTheory.V.Z.Sym.Sig.OkDOrb := UpperTheory.V.Z.Sym.Sig.diagonal_orbit_admissible

end
