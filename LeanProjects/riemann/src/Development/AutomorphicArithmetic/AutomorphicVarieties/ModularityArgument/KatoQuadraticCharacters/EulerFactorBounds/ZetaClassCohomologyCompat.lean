import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CohApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.TopRel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.RepSlD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SXiCoh
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.XiDist
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCycZ

open scoped MatrixGroups Matrix Classical
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb.NormOneIndex

private theorem frac (M M' : ℕ) [NeZero M] (h : M' = M) (a : ℤ) (z : ZMod M) (hz : (a : ZMod M) = z) :
    ∃ j : ℤ, (a : ℚ) / (M' : ℚ) = (z.val : ℚ) / M + j := by
  rw [h]
  subst hz
  refine ⟨a / (M : ℤ), ?_⟩
  have hv : (((a : ZMod M).val : ℤ)) = a % (M : ℤ) := ZMod.val_intCast a
  have hM : (M : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hv' : (((a : ZMod M).val : ℕ) : ℚ) = ((a % (M : ℤ) : ℤ) : ℚ) := by exact_mod_cast hv
  have key : (a : ℚ) = ((a % (M : ℤ) : ℤ) : ℚ) + (M : ℚ) * ((a / (M : ℤ) : ℤ) : ℚ) := by
    have := Int.mul_ediv_add_emod a (M : ℤ)
    have h2 : (M : ℚ) * ((a / (M : ℤ) : ℤ) : ℚ) + ((a % (M : ℤ) : ℤ) : ℚ) = (a : ℚ) := by
      exact_mod_cast this
    linarith
  rw [hv', key]
  field_simp

private theorem topT_step (l L N : ℕ) [NeZero N] (h : Nat.Coprime l N) :
    ((topT l (L + 1) N * l ^ (L + 1) : ℕ) : ZMod (N * l ^ L)) = ((topT l L N * l ^ L : ℕ) : ZMod (N * l ^ L)) := by
  have hu : IsUnit (l : ZMod N) := (ZMod.isUnit_iff_coprime l N).2 h
  have hone : ∀ s, ((topT l s N * l ^ s : ℕ) : ZMod N) = 1 := by
    intro s
    simp only [topT, Nat.cast_mul, Nat.cast_pow, ZMod.natCast_zmod_val]
    exact ZMod.inv_mul_of_unit _ (hu.pow s)
  have hcop : N.Coprime (l ^ L) := (Nat.Coprime.pow_left L h).symm
  rw [ZMod.natCast_eq_natCast_iff]
  refine (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨?_, ?_⟩
  · rw [← ZMod.natCast_eq_natCast_iff, hone, hone]
  · have h1 : l ^ L ∣ topT l (L + 1) N * l ^ (L + 1) :=
      Dvd.dvd.mul_left (pow_dvd_pow l (Nat.le_succ L)) _
    have h2 : l ^ L ∣ topT l L N * l ^ L := dvd_mul_left _ _
    exact (Nat.modEq_zero_iff_dvd.2 h1).trans (Nat.modEq_zero_iff_dvd.2 h2).symm

private theorem two_ne (l N M : ℕ) [Fact l.Prime] (hl : l ≠ 2) (h : Nat.Coprime l N) (hd : l ∣ M) (x : Row M) (i : Fin 2)
    (hx : ZMod.castHom hd (ZMod l) (x i) = (N : ZMod l)) : (2 : ZMod M) • x ≠ 0 := by
  intro h0
  have h1 : (2 : ZMod M) * x i = 0 := by
    have := congrFun h0 i
    simpa [smul_eq_mul] using this
  have h2 : (2 : ZMod l) * (N : ZMod l) = 0 := by
    have := congrArg (ZMod.castHom hd (ZMod l)) h1
    rw [map_mul, map_ofNat, map_zero, hx] at this
    exact this
  have h2' : (2 : ZMod l) ≠ 0 := by
    intro h2z
    have h3 : ((2 : ℕ) : ZMod l) = 0 := by exact_mod_cast h2z
    rw [ZMod.natCast_eq_zero_iff] at h3
    exact hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h3)
  have hN : (N : ZMod l) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).1 h
  exact mul_ne_zero h2' hN h2

private def rx (l L N M : ℕ) (x : ZMod N) : Row M := ![((N + x.val * (topT l L N * l ^ L) : ℕ) : ZMod M), 0]
private def ry (l L N M : ℕ) : Row M := ![((topT l L N * l ^ L : ℕ) : ZMod M), (N : ZMod M)]

private theorem castHom_rx_zero_eq_natCast (l L N M : ℕ) (x : ZMod N) (hd : l ∣ M) (hL : L ≠ 0) :
    ZMod.castHom hd (ZMod l) (rx l L N M x 0) = (N : ZMod l) := by
  simp only [rx, Matrix.cons_val_zero, map_natCast]
  push_cast
  simp [ZMod.natCast_self, zero_pow hL]

private theorem castHom_ry_one_eq_natCast (l L N M : ℕ) (hd : l ∣ M) :
    ZMod.castHom hd (ZMod l) (ry l L N M 1) = (N : ZMod l) := by
  simp [ry]

private theorem ok (l L N M : ℕ) [Fact l.Prime] (x : ZMod N) (hl : l ≠ 2) (h : Nat.Coprime l N) (hd : l ∣ M) (hL : L ≠ 0) :
    Ok (rx l L N M x) (ry l L N M) := by
  refine ⟨?_, ?_⟩
  · intro h0
    apply two_ne l N M hl h hd _ 0 (castHom_rx_zero_eq_natCast l L N M x hd hL)
    simp only [two_nsmul, two_smul] at h0 ⊢
    exact h0
  · intro h0
    apply two_ne l N M hl h hd _ 1 (castHom_ry_one_eq_natCast l L N M hd)
    simp only [two_nsmul, two_smul] at h0 ⊢
    exact h0

private theorem bas (l L N M : ℕ) [Fact l.Prime] [NeZero M] (x : ZMod N) (h : Nat.Coprime l N) (hd : l ∣ M) (hL : L ≠ 0) :
    Bas l N (rx l L N M x) (ry l L N M) := by
  refine ⟨h, ?_⟩
  have hN : (N : ZMod l) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).1 h
  have cv : ∀ v : ZMod M, ((v.val : ℕ) : ZMod l) = ZMod.castHom hd (ZMod l) v := by
    intro v
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  have hx1 : rx l L N M x 1 = 0 := by simp [rx]
  rw [hx1, ZMod.val_zero, cv, cv, castHom_rx_zero_eq_natCast l L N M x hd hL, castHom_ry_one_eq_natCast l L N M hd]
  simp only [Nat.cast_zero, zero_mul, sub_zero]
  exact mul_ne_zero hN hN

private theorem ix (l L N M : ℕ) [NeZero M] (x : ZMod N) (h : N * l ^ L = M) :
    (∀ i, ∃ j : ℤ, ixU l L N x i = toQ M (rx l L N M x) i + j) ∧ ∀ i, ∃ j : ℤ, ixV l L N i = toQ M (ry l L N M) i + j := by
  refine ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
  · obtain ⟨j, hj⟩ := frac M (N * l ^ L) h ((N + x.val * (topT l L N * l ^ L) : ℕ) : ℤ)
      (rx l L N M x 0) (by rw [Int.cast_natCast]; rfl)
    refine ⟨j, ?_⟩
    simp only [toQ]
    rw [← hj]
    simp only [ixU, Matrix.cons_val_zero]
    push_cast
    ring
  · exact ⟨0, by simp [ixU, toQ, rx]⟩
  · obtain ⟨j, hj⟩ := frac M (N * l ^ L) h ((topT l L N * l ^ L : ℕ) : ℤ)
      (ry l L N M 0) (by rw [Int.cast_natCast]; rfl)
    refine ⟨j, ?_⟩
    simp only [toQ]
    rw [← hj]
    simp only [ixV, Matrix.cons_val_zero]
    push_cast
    ring
  · obtain ⟨j, hj⟩ := frac M (N * l ^ L) h ((N : ℕ) : ℤ)
      (ry l L N M 1) (by rw [Int.cast_natCast]; rfl)
    refine ⟨j, ?_⟩
    simp only [toQ]
    rw [← hj]
    simp only [ixV, Matrix.cons_val_one, Matrix.head_cons]
    push_cast
    ring

private theorem dn_rows (l L N : ℕ) [NeZero N] (x : ZMod N) (h : Nat.Coprime l N) :
    dn l (N * l ^ L) (rx l (L + 1) N _ x) = rx l L N _ x ∧ dn l (N * l ^ L) (ry l (L + 1) N _) = ry l L N _ := by
  have e := topT_step l L N h
  push_cast at e
  constructor
  · funext i
    fin_cases i
    · simp [Sym.dn, rx, e, -ZMod.natCast_val]
    · simp [Sym.dn, rx]
  · funext i
    fin_cases i
    · simp [Sym.dn, ry, e]
    · simp [Sym.dn, ry]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}

private theorem brg (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n r N M₀ w c d : ℕ) [NeZero N] [NeZero M₀] (x : ZMod N) (g : SL(2, ℤ))
    (H : Hyp l N c d g) (hn : 1 ≤ n) (hM : N * l ^ (r + n) = M₀) (hL : LiftsWith X l N w (cL X l N w)) (ws) (hw : Laws X l c d ws)
    (hv : Lv c d M₀) (π : (ZMod (topM l n r (N * N)))ˣ →* (ZMod (l ^ r))ˣ) (hπ : ∀ z, π z = redM l n r (N * N) z) :
    CohB X l N w n (fun s => (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) (Y0 X l n r N x c d w g)
      fun s t => Xi X l n N M₀ (topM l n r (N * N)) w g (rx l (r + n) N M₀ x) (ry l (r + n) N M₀) (fun z => π z = t) (ws n M₀ s) := by
  have hcop : l.Coprime N := H.cop
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hL0 : r + n ≠ 0 := by omega
  have hlM : l ∣ M₀ := by
    rw [← hM]
    exact Dvd.dvd.mul_left (dvd_pow_self l hL0) N
  have hok := ok l (r + n) N M₀ x H.odd hcop hlM hL0
  have hlev : Lev l n N M₀ (topM l n r (N * N)) g := by
    refine ⟨?_, ?_, ?_, hn, hcop, H.g0⟩
    · rw [← hM]
      simp only [topM]
      ring
    · rw [← hM]
      exact dvd_mul_right N _
    · rw [← hM]
      exact Dvd.dvd.mul_left (pow_dvd_pow l (by omega)) N
  obtain ⟨β, hβ, hz⟩ := sTopRel Ω ε X l n N M₀ (topM l n r (N * N)) w g hlev hL c d ws hw hv
    (rx l (r + n) N M₀ x) (ry l (r + n) N M₀) hok (ixU l (r + n) N x) (ixV l (r + n) N)
    (ix l (r + n) N M₀ x hM).1 (ix l (r + n) N M₀ x hM).2
  have hb := sBridge Ω ε X l n N M₀ (topM l n r (N * N)) w g hlev hL
    (rx l (r + n) N M₀ x) (ry l (r + n) N M₀) hok (ws n M₀) (hw.coc n M₀ hv)
    (clsG X l n N (topM l n r (N * N)) w c d g (ixU l (r + n) N x) (ixV l (r + n) N)) β hβ hz
    (ZMod (l ^ r))ˣ π
  have hκ : (fun s => (π (cycM (topM l n r (N * N)) s))⁻¹) =
      (fun s => (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) := by
    funext s
    rw [hπ, (sCycZ Ω l r s).1]
    congr 1
    simp only [redM]
    exact ((sSlD Ω ε X N hN0).2.2.2.2.2.2.2 (topM l n r (N * N)) s).2.2.2.2 (l ^ r) _
  have hred : (⇑π) = redM l n r (N * N) := funext hπ
  have hpush : GlobalTheory.KA.push (⇑π) (shB X l (topM l n r (N * N))
      (clsG X l n N (topM l n r (N * N)) w c d g (ixU l (r + n) N x) (ixV l (r + n) N))) =
      Y0 X l n r N x c d w g := by
    rw [hred]
    rfl
  rw [hκ, hpush] at hb
  exact hb

end UpperTheory.V.Z.Kato.Nb.NormOneIndex

private theorem algebraMap_int_F_to_K_eq_algebraMap_F_K {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}
    (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (r T N : ℕ) [NeZero T] (hN : 0 < N) (hT : l ^ r ∣ T)
    (π : (ZMod T)ˣ →* (ZMod (l ^ r))ˣ)
    (hπ : ∀ z, π z = Units.map (ZMod.castHom hT (ZMod (l ^ r)) : ZMod T →* ZMod (l ^ r)) z) :
    (fun s => (π (cycM T s))⁻¹) = (fun s => (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) := by
  funext s
  rw [hπ, (sCycZ Ω l r s).1]
  congr 1
  exact ((sSlD Ω ε X N hN).2.2.2.2.2.2.2 T s).2.2.2.2 (l ^ r) hT

open UpperTheory.V.Z.Kato.Nb.NormOneIndex in
theorem UpperTheory.V.Z.Kato.Nb.katoZetaElement_normCompatible_in_lTower :
    UpperTheory.V.Z.Kato.Nb.KatoClassCompatibleModPowers := by
  intro Ω _ _ _ ε X l _ N _ x c d w g H hws hL n r
  obtain ⟨ws, hw⟩ := hws
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hl0 : 0 < l := (Fact.out : l.Prime).pos
  have hcop : l.Coprime N := H.cop
  have api := fun k => sCohApi Ω ε X l N w k hN0 (ZMod (l ^ r))ˣ
    (fun s => (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact (api 0).2.2.2.2.2.1 _ _
  have hn1 : 1 ≤ n := hn
  have cN : c.Coprime N := Nat.Coprime.coprime_dvd_right (dvd_mul_left N (6 * l)) H.cc
  have cl : c.Coprime l :=
    Nat.Coprime.coprime_dvd_right (dvd_mul_of_dvd_left (dvd_mul_left l 6) N) H.cc
  have dN : d.Coprime N := Nat.Coprime.coprime_dvd_right (dvd_mul_left N (6 * l)) H.cd
  have dl : d.Coprime l :=
    Nat.Coprime.coprime_dvd_right (dvd_mul_of_dvd_left (dvd_mul_left l 6) N) H.cd
  have lv0 : Lv c d (N * l ^ (r + n)) :=
    ⟨Nat.mul_pos hN0 (pow_pos hl0 _), Nat.Coprime.mul_right cN (Nat.Coprime.pow_right _ cl),
      Nat.Coprime.mul_right dN (Nat.Coprime.pow_right _ dl)⟩
  have lv1 : Lv c d (l * (N * l ^ (r + n))) :=
    ⟨Nat.mul_pos hl0 lv0.1, Nat.Coprime.mul_right cl lv0.2.1, Nat.Coprime.mul_right dl lv0.2.2⟩
  have hT0 : l ^ r ∣ topM l n r (N * N) := by
    show l ^ r ∣ l ^ (r + n) * (N * N)
    exact dvd_mul_of_dvd_left (pow_dvd_pow l (Nat.le_add_right r n)) _
  have hT1 : l ^ r ∣ topM l (n + 1) r (N * N) := by
    show l ^ r ∣ l ^ (r + (n + 1)) * (N * N)
    exact dvd_mul_of_dvd_left (pow_dvd_pow l (Nat.le_add_right r (n + 1))) _
  have hTT : topM l n r (N * N) ∣ topM l (n + 1) r (N * N) := ⟨l, by simp only [topM]; ring⟩
  have hT1eq : topM l (n + 1) r (N * N) = N * (l * (N * l ^ (r + n))) := by
    simp only [topM]
    ring
  obtain ⟨π0, hπ0⟩ : ∃ π : (ZMod (topM l n r (N * N)))ˣ →* (ZMod (l ^ r))ˣ, ∀ z, π z =
      Units.map (ZMod.castHom hT0 (ZMod (l ^ r)) : ZMod (topM l n r (N * N)) →* ZMod (l ^ r)) z :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨π1, hπ1⟩ : ∃ π : (ZMod (topM l (n + 1) r (N * N)))ˣ →* (ZMod (l ^ r))ˣ, ∀ z, π z =
      Units.map (ZMod.castHom hT1 (ZMod (l ^ r)) : ZMod (topM l (n + 1) r (N * N)) →* ZMod (l ^ r)) z :=
    ⟨_, fun _ => rfl⟩
  have hπ01 : ∀ z, π1 z = π0 (Units.map (ZMod.castHom hTT (ZMod (topM l n r (N * N))) :
      ZMod (topM l (n + 1) r (N * N)) →* ZMod (topM l n r (N * N))) z) := by
    intro z
    rw [hπ1, hπ0]
    ext
    simp only [Units.coe_map, MonoidHom.coe_coe]
    exact (RingHom.congr_fun (Subsingleton.elim
      ((ZMod.castHom hT0 (ZMod (l ^ r))).comp (ZMod.castHom hTT (ZMod (topM l n r (N * N)))))
      (ZMod.castHom hT1 (ZMod (l ^ r)))) (z : ZMod _)).symm
  have hlev0 : Lev l n N (N * l ^ (r + n)) (topM l n r (N * N)) g :=
    ⟨by simp only [topM]; ring, dvd_mul_right N _, ⟨N * l ^ r, by ring⟩, hn1, hcop, H.g0⟩
  have hlev1 : Lev l n N (l * (N * l ^ (r + n))) (topM l (n + 1) r (N * N)) g :=
    ⟨by simp only [topM]; ring, ⟨l * l ^ (r + n), by ring⟩, ⟨l * N * l ^ r, by ring⟩, hn1, hcop, H.g0⟩
  have ok0 := ok l (r + n) N (N * l ^ (r + n)) x H.odd hcop
    (Dvd.dvd.mul_left (dvd_pow_self l (by omega)) N) (by omega)
  have ok1 := ok l (r + (n + 1)) N (l * (N * l ^ (r + n))) x H.odd hcop (dvd_mul_right l _) (by omega)
  have hbas := bas l (r + (n + 1)) N (l * (N * l ^ (r + n))) x hcop (dvd_mul_right l _) (by omega)
  have hdn : Sym.dn l (N * l ^ (r + n)) (rx l (r + (n + 1)) N (l * (N * l ^ (r + n))) x) =
        rx l (r + n) N (N * l ^ (r + n)) x ∧
      Sym.dn l (N * l ^ (r + n)) (ry l (r + (n + 1)) N (l * (N * l ^ (r + n)))) =
        ry l (r + n) N (N * l ^ (r + n)) :=
    dn_rows l (r + n) N x hcop
  have A := brg X l (n + 1) r N (l * (N * l ^ (r + n))) w c d x g H (by omega) (by ring) hL ws hw lv1
    π1 (fun z => by rw [hπ1]; rfl)
  have A' := (api n).2.2.2.2.1 _ _ A
  have F := brg X l n r N (N * l ^ (r + n)) w c d x g H hn1 rfl hL ws hw lv0
    π0 (fun z => by rw [hπ0]; rfl)
  have B := (api n).2.1
    (fun s t => Xi X l (n + 1) N (l * (N * l ^ (r + n))) (topM l (n + 1) r (N * N)) w g
      (rx l (r + (n + 1)) N (l * (N * l ^ (r + n))) x) (ry l (r + (n + 1)) N (l * (N * l ^ (r + n))))
      (fun z => π1 z = t) (ws (n + 1) (l * (N * l ^ (r + n))) s))
    (fun s t => Xi X l n N (l * (N * l ^ (r + n))) (topM l (n + 1) r (N * N)) w g
      (rx l (r + (n + 1)) N (l * (N * l ^ (r + n))) x) (ry l (r + (n + 1)) N (l * (N * l ^ (r + n))))
      (fun z => π1 z = t) (ws (n + 1) (l * (N * l ^ (r + n))) s))
    (fun s t => (sXiMul Ω ε X l n N (l * (N * l ^ (r + n))) (topM l (n + 1) r (N * N)) w g hlev1
      _ _ ok1 (fun z => π1 z = t)).2.2.1 _)
  have C := sXiCoh Ω ε X l n N (l * (N * l ^ (r + n))) (topM l (n + 1) r (N * N)) w g hlev1 hL
    _ _ ok1 (ZMod (l ^ r))ˣ π1 (ws (n + 1) (l * (N * l ^ (r + n)))) (ws n (l * (N * l ^ (r + n))))
    (hw.red n _ lv1)
  rw [algebraMap_int_F_to_K_eq_algebraMap_F_K X l r (topM l (n + 1) r (N * N)) N hN0 hT1 π1 hπ1] at C
  have D := (api n).2.1
    (fun s t => Xi X l n N (l * (N * l ^ (r + n))) (topM l (n + 1) r (N * N)) w g
      (rx l (r + (n + 1)) N (l * (N * l ^ (r + n))) x) (ry l (r + (n + 1)) N (l * (N * l ^ (r + n))))
      (fun z => π1 z = t) (ws n (l * (N * l ^ (r + n))) s))
    (fun s t => Xi X l n N (N * l ^ (r + n)) (topM l n r (N * N)) w g
      (rx l (r + n) N (N * l ^ (r + n)) x) (ry l (r + n) N (N * l ^ (r + n)))
      (fun z => π0 z = t) (pushD X l (N * l ^ (r + n)) (ws n (l * (N * l ^ (r + n))) s)))
    (by
      intro s t
      have h1 := sXiDist Ω ε X l n N (N * l ^ (r + n)) (topM l n r (N * N)) w g hlev0
        (topM l (n + 1) r (N * N)) hTT hT1eq _ _ hbas (fun z => π0 z = t) (ws n (l * (N * l ^ (r + n))) s)
      rw [hdn.1, hdn.2] at h1
      have hP : (fun z => π1 z = t) = (fun z => π0 (Units.map (ZMod.castHom hTT
          (ZMod (topM l n r (N * N))) : ZMod (topM l (n + 1) r (N * N)) →* ZMod (topM l n r (N * N))) z) = t) :=
        funext fun z => by rw [hπ01]
      beta_reduce
      rw [hP]
      exact h1)
  have E := sXiCoh Ω ε X l n N (N * l ^ (r + n)) (topM l n r (N * N)) w g hlev0 hL
    _ _ ok0 (ZMod (l ^ r))ˣ π0 (fun s => pushD X l (N * l ^ (r + n)) (ws n (l * (N * l ^ (r + n))) s))
    (ws n (N * l ^ (r + n))) (hw.dist n l _ lv1)
  rw [algebraMap_int_F_to_K_eq_algebraMap_F_K X l r (topM l n r (N * N)) N hN0 hT0 π0 hπ0] at E
  have eqv := (api n).1
  exact eqv.trans (eqv.trans (eqv.trans (eqv.trans (eqv.trans A' B) C) D) E) (eqv.symm F)
