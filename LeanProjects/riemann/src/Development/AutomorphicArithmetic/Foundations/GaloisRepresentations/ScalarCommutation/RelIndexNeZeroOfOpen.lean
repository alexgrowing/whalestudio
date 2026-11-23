import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ExistsIdempotentHeckeOperatorWithRegularSupportAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.FacEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.InvTMemSim
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PLocComm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PKNOpen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PKNIdx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PKNIff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PLatCoord
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRepLaws
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriAndMaximalCompactCriteria

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp cj lev GLw mat sim)
open UpperTheory.Gal.LocalSmoothExtension UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl
open GlobalTheory.LFun (KGL)
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Spc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}
variable {x : E} {U : Submodule ℂ (UA E n → ℂ)} {w₀ : Plc E} {Up : Plc E → Prop}

private theorem th_eq (F : Frame S) (g : GUf E n) : F.th g = CertificateRingHomMap.th g :=
  Subtype.ext (Prod.ext (Units.ext (F.th_mat g)) (F.th_sim g))

private theorem continuous_th : Continuous (CertificateRingHomMap.th : GUf E n → GUf E n) := by
  refine continuous_induced_rng.2 ?_
  exact ((GlobalTheory.SplitPts.continuous_invT _).comp (continuous_fst.comp continuous_subtype_val)).prodMk
    (continuous_inv.comp (continuous_snd.comp continuous_subtype_val))

private theorem relIndex_ne_zero_of_open {X : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    {K O : Subgroup X} (hK : IsCompact (K : Set X)) (hO : IsOpen (O : Set X)) : O.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have ho : IsOpen ((O.subgroupOf K : Subgroup K) : Set K) := hO.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ ho
  exact Nat.card_pos.ne'

private theorem isCompact_comap_th (F : Frame S) {K : Subgroup (GUf E n)} (hK : IsCompact (K : Set (GUf E n))) :
    IsCompact ((K.comap F.th : Subgroup (GUf E n)) : Set (GUf E n)) := by
  convert hK.image continuous_th using 1
  ext g
  constructor
  · intro h
    refine ⟨F.th g, h, ?_⟩
    rw [th_eq, UpperTheory.Gal.CertificateRingHomMap.th_th]
  · rintro ⟨y, hy, rfl⟩
    show F.th (CertificateRingHomMap.th y) ∈ K
    rw [th_eq, UpperTheory.Gal.CertificateRingHomMap.th_th]
    exact hy

private theorem relIdx (F : Frame S) {K : Subgroup (GUf E n)} (hK : IsCompact (K : Set (GUf E n))) (N : ℕ) (hN : 0 < N) :
    (S.L.KN N).relIndex ((K.comap F.th).map F.j) ≠ 0 := by
  rw [← Subgroup.relIndex_comap]
  have hO := pKNOpen (pKNIff (pLatCoord pRepLaws)) E A n p S F.tr N hN
  rw [← F.j_tr] at hO
  exact relIndex_ne_zero_of_open (isCompact_comap_th F hK) hO

private theorem cong_at (F : Frame S) (k : GUf E n) (N : ℕ) (hN : 0 < N) (hk : S.L.CongOne N (F.j k)) (w : Plc E)
    (hp : (p : 𝓞 E) ∉ w.asIdeal) : Cong1 N w (F.a w * comp w k * (F.a w)⁻¹) := by
  have h := ((pKNIff (pLatCoord pRepLaws)) E A n p S F.tr k).2 N hN
  rw [← F.j_tr] at h
  have := h.1 hk w hp
  rw [map_mul, map_mul, map_inv, ← F.a_tr] at this
  exact this

private theorem val_nat_lt_one {w : Plc E} {r N : ℕ} (hr : (r : 𝓞 E) ∈ w.asIdeal) (hN : r ∣ N) :
    Valued.v (N : w.adicCompletion E) < 1 := by
  have h1 : (N : 𝓞 E) ∈ w.asIdeal := by
    obtain ⟨c, rfl⟩ := hN
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hr
  have h2 := (w.valuation_lt_one_iff_mem (K := E) (N : 𝓞 E)).2 h1
  have e : (N : w.adicCompletion E) = algebraMap E (w.adicCompletion E) (algebraMap (𝓞 E) E (N : 𝓞 E)) := by
    rw [map_natCast, map_natCast]
  rw [e]
  exact (w.valuedAdicCompletion_eq_valuation' _).trans_lt h2

private theorem mul_lt_left {w : Plc E} {A B : Matrix (Fin n) (Fin n) (w.adicCompletion E)}
    (hA : ∀ i j, Valued.v (A i j) ≤ 1) (hB : ∀ i j, Valued.v (B i j) < 1) (i j : Fin n) : Valued.v ((A * B) i j) < 1 := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_mul' (hA _ _) le_rfl) (by simpa using hB l j)

private theorem mul_lt_right {w : Plc E} {A B : Matrix (Fin n) (Fin n) (w.adicCompletion E)}
    (hA : ∀ i j, Valued.v (A i j) < 1) (hB : ∀ i j, Valued.v (B i j) ≤ 1) (i j : Fin n) : Valued.v ((A * B) i j) < 1 := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_mul' le_rfl (hB _ _)) (by simpa using hA i l)

private theorem sub_lt_of_conj {w : Plc E} (a g : GLw n w) (ha : a ∈ KGL w n)
    (h : ∀ i k, Valued.v (((a * g * a⁻¹).val - 1) i k) < 1) (i k : Fin n) : Valued.v ((g.val - 1) i k) < 1 := by
  have hK := ((GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n a).2).1 ha
  have e : g.val - 1 = (a⁻¹).val * ((a * g * a⁻¹).val - 1) * a.val := by
    have h1 : (a⁻¹).val * a.val = 1 := by simp
    have h2 : (a⁻¹).val * (a * g * a⁻¹).val * a.val = g.val := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    rw [Matrix.mul_sub, Matrix.sub_mul, h2, Matrix.mul_one, h1]
  rw [e]
  exact mul_lt_right (mul_lt_left hK.2 h) hK.1 i k

private theorem le_one_of_sub_lt {w : Plc E} {g : GLw n w} (h : ∀ i k, Valued.v ((g.val - 1) i k) < 1) (i k : Fin n) :
    Valued.v (g.val i k) ≤ 1 := by
  have e : g.val i k = (g.val - 1) i k + (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i k := by simp
  rw [e]
  refine (Valuation.map_add _ _ _).trans (max_le (h i k).le ?_)
  by_cases hik : i = k <;> simp [hik, Matrix.one_apply]

private theorem iw_of_cong {w : Plc E} (a g : GLw n w) (ha : a ∈ KGL w n)
    (h : ∀ i k, Valued.v (((a * g * a⁻¹).val - 1) i k) < 1)
    (h' : ∀ i k, Valued.v (((a * g⁻¹ * a⁻¹).val - 1) i k) < 1) : g ∈ Iw n w := by
  have c1 := sub_lt_of_conj a g ha h
  have c2 := sub_lt_of_conj a g⁻¹ ha h'
  refine ((GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n g).1).2 ⟨le_one_of_sub_lt c1, le_one_of_sub_lt c2, fun i j hij => ?_⟩
  have e : g.val i j = (g.val - 1) i j := by
    simp [Matrix.one_apply, (ne_of_lt hij).symm]
  rw [e]
  exact c1 i j

end UpperTheory.Gal.Spc

open UpperTheory.Gal.Spc in
theorem UpperTheory.Gal.Spc.tyEx :
    UpperTheory.Gal.Spc.TyEx := by
  intro E _ _ _ A n p _ S F x U w₀ Up V hOff r W hAux N hrN hSt
  have hS0 : w₀ ∈ V.S := V.shape.mem
  have hw : IsSplitAt w₀ ∧ (p : 𝓞 E) ∉ w₀.asIdeal := ⟨V.split, hOff.1 w₀ hS0⟩
  have hN : 0 < N.1 := lt_of_lt_of_le (by norm_num) N.2.1
  haveI : Fact r.Prime := ⟨hAux.prime⟩
  choose L hL using fun w : Spl E p => facEx E A n p S F w
  have hcomp : ∀ (u : Plc E) (g : GUf E n), comp u (F.th g) = invT n _ (comp u g) := fun u g => by
    rw [th_eq, UpperTheory.Gal.CertificateRingHomMap.comp_th]
  let K : Subgroup S.G.GAf := ((lev V.S V.Kw).comap F.th).map F.j ⊓ ⨅ w ∈ W, (Iw n w.1).comap (L w).pr
  have hK : ∀ k, k ∈ K ↔ (∃ k', F.j k' = k ∧ F.th k' ∈ lev V.S V.Kw) ∧ ∀ w ∈ W, (L w).pr k ∈ Iw n w.1 := by
    intro k
    simp only [K, Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_iInf, Subgroup.mem_comap]
    exact and_congr_left' (exists_congr fun _ => and_comm)
  obtain ⟨-, hap, -, -, hcc, -⟩ := UpperTheory.Gal.CertificateRingHomMap.pLocComm_of E n w₀ hw.1
  have hfact : (L ⟨w₀, hw⟩).Fact K (V.J.comap (invT n _)) := by
    refine ⟨fun y hy => (hK _).2 ⟨⟨CertificateRingHomMap.loc hw.1 y, ((hL ⟨w₀, hw⟩).2 y).symm, ?_⟩, fun w hW => ?_⟩, fun g hg => ?_⟩
    · refine UpperTheory.Gal.CertificateRingHomMap.mem_lev.2 ⟨?_, fun u hu => ?_, fun u hu hu' => ?_⟩
      · rw [F.th_sim, UpperTheory.Gal.CertificateRingHomMap.sim_loc, inv_one]
        exact one_mem _
      · rw [hcomp]
        by_cases h1 : u = w₀
        · subst h1
          rw [UpperTheory.Gal.CertificateRingHomMap.comp_loc, V.Kw0]
          exact hy
        · have h2 : u ≠ cj w₀ := fun h => (V.shape.up w₀ hS0 V.split).2 (h ▸ hu)
          rw [UpperTheory.Gal.CertificateRingHomMap.comp_loc_of_apart hw.1 ((hap u).2 ⟨h1, h2⟩), map_one]
          exact one_mem _
      · have h1 : u ≠ w₀ := fun h => hu (h ▸ hS0)
        have h2 : u ≠ cj w₀ := fun h => hu' (by rw [h, hcc]; exact hS0)
        rw [hcomp, UpperTheory.Gal.CertificateRingHomMap.comp_loc_of_apart hw.1 ((hap u).2 ⟨h1, h2⟩), map_one]
        exact one_mem _
    · have e : (L ⟨w₀, hw⟩).loc y = F.j (CertificateRingHomMap.loc hw.1 y) := (hL ⟨w₀, hw⟩).2 y
      rw [e, (hL w).1, UpperTheory.Gal.CertificateRingHomMap.comp_loc_of_apart hw.1 (apart_of_not_mem (hAux.off w₀ hS0) (hAux.half.above w hW))]
      exact one_mem _
    · obtain ⟨⟨k', rfl, hk'⟩, -⟩ := (hK g).1 hg
      have e : (L ⟨w₀, hw⟩).pr (F.j k') = comp w₀ k' := (hL ⟨w₀, hw⟩).1 k'
      have h := (UpperTheory.Gal.CertificateRingHomMap.mem_lev.1 hk').2.1 w₀ hS0
      rw [hcomp, V.Kw0] at h
      rw [e]
      exact h
  have hle : S.L.KN N.1 ≤ K := by
    intro k hk
    obtain ⟨k', rfl, hk', -⟩ := hSt k hk
    refine (hK _).2 ⟨⟨k', rfl, hk'⟩, fun w hW => ?_⟩
    have hr := hAux.half.above w hW
    have hv := val_nat_lt_one hr hrN
    rw [(hL w).1]
    refine iw_of_cong (F.a w.1) _ (F.a_int w.1 r hAux.prime hAux.good hr) (fun i k => ?_) (fun i k => ?_)
    · exact (cong_at F k' N.1 hN hk.1 w.1 w.2.2 i k).trans_lt hv
    · have h := cong_at F k'⁻¹ N.1 hN (by rw [map_inv]; exact hk.2) w.1 w.2.2 i k
      rw [map_inv] at h
      exact h.trans_lt hv
  refine ⟨L, hw,
    { L := L ⟨w₀, hw⟩
      K := K
      K₀ := S.L.KN N.1
      J := V.J.comap (invT n _)
      ψ := V.χ.comp ((invT n _).subgroupComap V.J)
      fact := hfact
      le := hle
      ker := fun k hk h => ?_
      idx := fun h0 => relIdx F V.cpt N.1 hN (Subgroup.relIndex_eq_zero_of_le_right inf_le_left h0)
      cms := (pKNIdx (pKNOpen (pKNIff (pLatCoord pRepLaws))) E A n p S F.tr N.1 hN).1 },
    ⟨hL, rfl, rfl, hK, fun y y' h => ?_, fun y y' h => ?_⟩⟩
  · obtain ⟨k', rfl, -, hJ, hχ⟩ := hSt k hk
    rw [← hχ]
    refine congrArg V.χ (Subtype.ext ?_)
    show invT n _ ((L ⟨w₀, hw⟩).pr (F.j k')) = comp w₀ (F.th k')
    rw [hcomp]
    exact congrArg _ ((hL ⟨w₀, hw⟩).1 k')
  · have e : y' = invT n _ y := Units.ext h
    rw [e]
    rfl
  · exact congrArg V.χ (Subtype.ext (Units.ext h.symm))
