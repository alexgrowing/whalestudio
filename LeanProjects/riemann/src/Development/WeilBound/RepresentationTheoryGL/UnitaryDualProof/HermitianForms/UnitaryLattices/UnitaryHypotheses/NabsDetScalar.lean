import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.TopMain
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.DerCharBlkAtMirU

noncomputable section

set_option linter.unusedSectionVars false

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir GlobalTheory.LocGL GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Form.U.Asm

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U PositivityTheory.RgUd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem gLEq_congr {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V}
    {a b : ℕ} (hab : a = b) {ha : a + 1 ≤ N} {hb : b + 1 ≤ N} {s : ℝ} {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
    (h : GLEq k π a ha s B) : GLEq k π b hb s B := by
  subst hab; exact h

theorem isAtom_congr {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V}
    {a b : ℕ} (hab : a = b) {ha : a + 2 ≤ N} {hb : b + 2 ≤ N} {B B₀ : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
    (h : IsAtom ha π B B₀) : IsAtom hb π B B₀ := by
  subst hab; exact h

theorem scalAt_eq (n N : ℕ) (h : n ≤ N) (z : kˣ) :
    scalAt k n N h z = blkAt k n N h (GeneralLinearGroup.scalar (Fin n) z) := by
  unfold scalAt
  congr 1

theorem nabs_det_scalar (n : ℕ) (z : kˣ) :
    nabs k (GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin n) z)) = nabs k z ^ n := by
  rw [GeneralLinearGroup.det_scalar, Fintype.card_fin]
  simp [nabs, map_pow]

theorem derivTop_of (hUA : UAtom k) (hUD : UDens k) (hUS : USplit k) (hUL : ULift k) (hUAd : UAdm k)
    (hTB : ThmB k) : DerivTop k := by
  intro ψ hψc hψ1 n h π hh1 hsm hirr hunit hnt hsub
  obtain ⟨j, rfl⟩ : ∃ j, h = j + 1 := ⟨h - 1, by omega⟩
  obtain ⟨B, hBh, hBp, hBi⟩ := hunit
  have hB : IsInvForm π.ρ B := ⟨hBh, hBp, hBi⟩
  obtain ⟨q, hqs, hqk, hqe⟩ := derDict ψ n j π.ρ
  have hvan : ∀ n', n' < n → twKer π.ρ (derUnip k (n + (j + 1)) n') (derChar k ψ (n + (j + 1)) n') = ⊤ := by
    intro n' hn'
    have e : n + (j + 1) = n' + ((n + j - n') + 1) := by omega
    exact (cast_twKer ψ e π n').1 ((sub_iff_twKer ψ n' (n + j - n') (π.cast e)).1 (hsub n' _ e (by omega)))
  have hE1 : IsPsd (chain hUD hψc hψ1 π.ρ hsm B j) := chain_psd hUD hψc hψ1 π.ρ hsm B hB j (by omega)
  have hker : twKer π.ρ (derUnip k (n + (j + 1)) (n + (j + 1) - j)) (lvlChar k ψ (n + (j + 1)) (n + (j + 1) - j)) ≤
      LinearMap.ker q := by
    rw [hqk, lvlChar_def, derChar_def]
    exact twKer_derUnip_le ψ π.ρ (a := n + (j + 1) - j) (b := n) (x := n + (j + 1) - j - 1) (y := n)
      (by omega) (by omega) (by omega)
  have hE3 : ∀ v, chain hUD hψc hψ1 π.ρ hsm B j v v = 0 → v ∈ LinearMap.ker q :=
    fun v hv => hker (chain_rad hUD hψc hψ1 π.ρ hsm B hB j (by omega) v hv)
  have hq2 : twKer π.ρ (derUnip k (n + (j + 1)) n) (derChar k ψ (n + (j + 1)) n) ≤ LinearMap.ker q := by
    rw [hqk]
    exact le_rfl

  have hE24 : (∀ v ∈ LinearMap.ker q, ∀ w, chain hUD hψc hψ1 π.ρ hsm B j v w = 0) ∧
      ∀ (g : GL (Fin n) k) v w, chain hUD hψc hψ1 π.ρ hsm B j (π.ρ (blkAt k n (n + (j + 1)) (by omega) g) v)
        (π.ρ (blkAt k n (n + (j + 1)) (by omega) g) w) =
        ((nabs k (GeneralLinearGroup.det g) ^ (j : ℝ) : ℝ) : ℂ) * chain hUD hψc hψ1 π.ρ hsm B j v w := by
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      refine ⟨fun v hv w => ?_, fun g v w => ?_⟩
      · have hK := chain_kills hUD hψc hψ1 π.ρ hsm B hB j (by omega)
        have e1 : 0 + (j + 1) - j = 1 := by omega
        rw [e1] at hK
        refine hK v ?_ w
        have hle : twKer π.ρ (derUnip k (0 + (j + 1)) 0) (derChar k ψ (0 + (j + 1)) 0) ≤
            twKer π.ρ (derUnip k (0 + (j + 1)) 1) (lvlChar k ψ (0 + (j + 1)) 1) :=
          twKer_mono π.ρ _ _ (le_inf inf_le_left (inf_le_left.trans (unipB_le_colFix_one _))) fun u => rfl
        rw [hqk] at hv
        exact hle hv
      · have hg : g = 1 := by
          ext i
          exact Fin.elim0 i
        subst hg
        simp [nabs]
    · obtain ⟨n₀, rfl⟩ : ∃ n₀, n = n₀ + 1 := ⟨n - 1, by omega⟩
      have hN2 : j + 2 ≤ n₀ + 1 + (j + 1) := by omega
      have h0 : ∀ v, chain hUD hψc hψ1 π.ρ hsm B (j + 1) v v = 0 := by
        by_contra hc
        push_neg at hc
        obtain ⟨n', hn', hne⟩ := twisted_kernel_forms_nonvanishing hUD hUA hψc hψ1 π.ρ hsm B hUS hB n₀ (j + 1) (by omega) hc
        exact hne (hvan n' (by omega))
      have hA := atom_eq_self hUD hUA hψc hψ1 π.ρ hsm B hUS hB j hN2 h0
      obtain ⟨-, -, -, hK, hG, -⟩ := atom_spec hUD hUA hψc hψ1 π.ρ hsm B j hN2
        (chain_lvl hUD hψc hψ1 π.ρ hsm B hB j hN2)
      rw [hA] at hK hG
      refine ⟨fun v hv w => ?_, fun g v w => ?_⟩
      · unfold DerKer at hK
        have e2 : n₀ + 1 + (j + 1) - 2 - j + 1 = n₀ + 1 := by omega
        rw [e2] at hK
        rw [hqk] at hv
        exact hK v hv w
      · have hG' : GLEq k π.ρ n₀ (by omega) (j : ℝ) (chain hUD hψc hψ1 π.ρ hsm B j) := gLEq_congr (by omega) hG
        exact hG' g v w
  obtain ⟨hE2, hE4⟩ := hE24
  refine top_core (by omega : n ≤ n + (j + 1)) π.ρ (derivB ψ (j + 1) π).ρ
    (hUAd ψ hψc hψ1 n (j + 1) π hsm hirr) q hqs hqe (j : ℝ) ((1 - ((j + 1 : ℕ) : ℝ)) / 2) (by push_cast; ring)
    (chain hUD hψc hψ1 π.ρ hsm B j) hE1 hE2 hE3 hE4 ?_
  intro C hC1 hC2 hC3 hC4
  refine lift hUD hψc hψ1 π.ρ hsm B hUL hTB hirr hB j (by omega) C hC1 (fun v hv w => hC2 v (hker hv) w) ?_ hC4
  refine mirEq_congr (a := n) (ha := by omega) (by omega) rfl ?_
  intro p hp v w
  obtain ⟨hact, hdet⟩ := mir_act ψ (by omega : n + 1 ≤ n + (j + 1)) π.ρ (derivB ψ (j + 1) π).ρ q hqe hq2 ⟨p, hp⟩
  have e : C (π.ρ (blkAt k (n + 1) (n + (j + 1)) (by omega) p) v) (π.ρ (blkAt k (n + 1) (n + (j + 1)) (by omega) p) w) =
      C (π.ρ (blkAt k n (n + (j + 1)) (by omega) (mirabolicProjection k n ⟨p, hp⟩)) v)
        (π.ρ (blkAt k n (n + (j + 1)) (by omega) (mirabolicProjection k n ⟨p, hp⟩)) w) :=
    factor hC1.1 q hC2 ((hact v).trans (hqe _ v).symm) ((hact w).trans (hqe _ w).symm)
  rw [e, hC3, ← hdet]

set_option maxHeartbeats 1000000 in

theorem derivPos_of (hUA : UAtom k) (hUD : UDens k) (hUS : USplit k) (hUL : ULift k) (hUSh : UShell k)
    (hUE : UEig k) (hTB : ThmB k) : DerivPos k := by
  intro ψ hψc hψ1 n i π hi hsm hirr hunit hex W _ _ σ ω hW hsq hcc z hz
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  obtain ⟨B, hBh, hBp, hBi⟩ := hunit
  have hB : IsInvForm π.ρ B := ⟨hBh, hBp, hBi⟩
  obtain ⟨n', h', e, hlt, hnt'⟩ := hex
  obtain ⟨j', rfl⟩ : ∃ j', h' = j' + 1 := ⟨h' - 1, by omega⟩
  have hne : twKer π.ρ (derUnip k (n + (j + 1)) n') (derChar k ψ (n + (j + 1)) n') ≠ ⊤ := by
    intro htop
    have h2 := (sub_iff_twKer ψ n' j' (π.cast e)).2 ((cast_twKer ψ e π n').2 htop)
    exact not_subsingleton _ h2
  obtain ⟨n₀, rfl⟩ : ∃ n₀, n = n₀ + 1 := ⟨n - 1, by omega⟩
  set t : ℝ := (1 - ((j + 1 : ℕ) : ℝ)) / 2 with ht
  obtain ⟨x, hx0, hxe⟩ := hUE ψ hψc hψ1 (n₀ + 1) (j + 1) π hsm hirr t W σ ω hW hsq hcc z
  obtain ⟨q, hqs, hqk, hqe⟩ := derDict ψ (n₀ + 1) j π.ρ
  obtain ⟨v, rfl⟩ := hqs x
  set g := GeneralLinearGroup.scalar (Fin (n₀ + 1)) z with hg
  set ct : ℂ := ((dpow (n₀ + 1) t g : ℂˣ) : ℂ) with hct
  have hct0 : ct ≠ 0 := Units.ne_zero _
  set c : ℂ := ct⁻¹ * (ω z : ℂ) with hc
  have hx0' : q v ≠ (0 : TwJacquet (iterPhi k ψ j (resM k π.ρ)).ρ (MirUin k (n₀ + 1)) 1) := hx0
  have hρ : GlobalTheory.BZMir.deriv k ψ j π.ρ g (q v) = c • q v := by
    have h1 : ct • GlobalTheory.BZMir.deriv k ψ j π.ρ g (q v) = (ω z : ℂ) • q v := hxe
    calc GlobalTheory.BZMir.deriv k ψ j π.ρ g (q v) = ct⁻¹ • (ct • GlobalTheory.BZMir.deriv k ψ j π.ρ g (q v)) := by
          rw [smul_smul, inv_mul_cancel₀ hct0, one_smul]
      _ = c • q v := by rw [h1, smul_smul]
  have hN2 : j + 2 ≤ n₀ + 1 + (j + 1) := by omega

  have hchne := chain_ne_of hUD hψc hψ1 π.ρ hsm B hB (j + 1) n' (by omega) (by omega) hne
  have hA0 := atom_eq_zero hUD hUA hψc hψ1 π.ρ hsm B hUS hUL hTB hirr hB j hN2 hchne
  have hAz : atom hUD hUA hψc hψ1 π.ρ hsm B j = 0 := by
    ext a b
    simp [hA0 a b]
  have hL := chain_lvl hUD hψc hψ1 π.ρ hsm B hB j hN2
  obtain ⟨hAt, -⟩ := atom_spec hUD hUA hψc hψ1 π.ρ hsm B j hN2 hL
  rw [hAz] at hAt
  have hL' : Lvl k ψ π.ρ n₀ (by omega) (j : ℝ) (chain hUD hψc hψ1 π.ρ hsm B j) := lvl_congr (by omega) rfl hL
  have hAt' : IsAtom (by omega : n₀ + 2 ≤ n₀ + 1 + (j + 1)) π.ρ (chain hUD hψc hψ1 π.ρ hsm B j) 0 :=
    isAtom_congr (by omega) hAt
  have hmem : π.ρ (scalAt k (n₀ + 1) (n₀ + 1 + (j + 1)) (by omega) z) v - c • v ∈ DerKer k ψ π.ρ n₀ := by
    have : π.ρ (scalAt k (n₀ + 1) (n₀ + 1 + (j + 1)) (by omega) z) v - c • v ∈ LinearMap.ker q := by
      rw [LinearMap.mem_ker, map_sub, map_smul, scalAt_eq]
      have h2 : q (π.ρ (blkAt k (n₀ + 1) (n₀ + 1 + (j + 1)) (by omega) g) v) = GlobalTheory.BZMir.deriv k ψ j π.ρ g (q v) :=
        hqe g v
      rw [h2, hρ, sub_self]
    rw [hqk] at this
    exact this
  have hnot : v ∉ DerKer k ψ π.ρ n₀ ⊔ LinearMap.ker (chain hUD hψc hψ1 π.ρ hsm B j) := by
    intro hv
    have hle : LinearMap.ker (chain hUD hψc hψ1 π.ρ hsm B j) ≤ DerKer k ψ π.ρ n₀ := by
      intro a ha
      have ha0 : chain hUD hψc hψ1 π.ρ hsm B j a a = 0 := by
        rw [LinearMap.mem_ker] at ha
        rw [ha]
        rfl
      have hr := chain_rad hUD hψc hψ1 π.ρ hsm B hB j (by omega) a ha0
      rw [lvlChar_def] at hr
      unfold DerKer
      rw [derChar_def]
      exact twKer_derUnip_le ψ π.ρ (a := n₀ + 1 + (j + 1) - j) (b := n₀ + 1) (x := n₀ + 1 + (j + 1) - j - 1)
        (y := n₀ + 1) (by omega) (by omega) (by omega) hr
    have hv' : v ∈ LinearMap.ker q := by
      rw [hqk]
      exact (sup_le le_rfl hle) hv
    exact hx0' (LinearMap.mem_ker.1 hv')
  have hsh := hUSh ψ hψc hψ1 n₀ (n₀ + 1 + (j + 1)) (by omega) π.V π.ρ hsm (j : ℝ)
    (chain hUD hψc hψ1 π.ρ hsm B j) hL' hAt' z c v hz hmem hnot

  have ha := nabs_pos k z
  set a := nabs k z with ha_def
  have hctv : ct = (((a ^ (n₀ + 1) : ℝ) ^ t : ℝ) : ℂ) := by
    rw [hct, dpow_val, hg, nabs_det_scalar]
  have hω : (ω z : ℂ) = c * ct := by
    rw [hc, mul_comm, ← mul_assoc, mul_inv_cancel₀ hct0, one_mul]
  have hnct : ‖ct‖ ^ 2 = a ^ (-(((n₀ : ℝ) + 1) * j)) := by
    rw [hctv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), ← Real.rpow_natCast a (n₀ + 1),
      ← Real.rpow_mul ha.le, ← Real.rpow_natCast _ 2, ← Real.rpow_mul ha.le, ht]
    congr 1
    push_cast
    ring
  have hprod : ‖(ω z : ℂ)‖ ^ 2 < 1 := by
    rw [hω, norm_mul, mul_pow, hnct]
    have hpos : 0 < a ^ (-(((n₀ : ℝ) + 1) * j)) := Real.rpow_pos_of_pos ha _
    calc ‖c‖ ^ 2 * a ^ (-(((n₀ : ℝ) + 1) * j)) < a ^ (((n₀ : ℝ) + 1) * j) * a ^ (-(((n₀ : ℝ) + 1) * j)) :=
          mul_lt_mul_of_pos_right hsh hpos
      _ = 1 := by rw [← Real.rpow_add ha, add_neg_cancel, Real.rpow_zero]
  nlinarith [norm_nonneg (ω z : ℂ)]

theorem uAsm : UAsm k := fun hUA hUD hUS hUL hUSh hUE hUAd hTB =>
  ⟨derivTop_of hUA hUD hUS hUL hUAd hTB, derivPos_of hUA hUD hUS hUL hUSh hUE hTB⟩

end PositivityTheory.RgUd.Form.U.Asm
