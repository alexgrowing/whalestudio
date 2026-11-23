import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelFormCompatBaseEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingFrameDeltaChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReducedBlockEqResidueDet
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DatEqOfPhiHat
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCuspIsThClsDUnique
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPsiTieOfValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitCOfCXiAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjSmulEntry
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RedMUMatMove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowZeroMulRightIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.Datum
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ClassSumRule

open GlobalTheory.LevelActionPinned GlobalTheory.GeoLevel GlobalTheory.DatumInverseCharacter

variable {D : D7}

theorem exists_unit_of_mem {B : Type} [CommRing B] (S : Subring B) {n : ℕ} (β g : GL (Fin n) B)
    (h1 : ∀ i j, (β⁻¹ * g * β).1 i j ∈ S) (h2 : ∀ i j, (β⁻¹ * g⁻¹ * β).1 i j ∈ S) :
    ∃ y : GL (Fin n) S, β.1 * y.1.map S.subtype * (β⁻¹).1 = g.1 := by
  let a : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨_, h1 i j⟩
  let b : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨_, h2 i j⟩
  have ha : S.subtype.mapMatrix a = (β⁻¹ * g * β).1 := rfl
  have hb : S.subtype.mapMatrix b = (β⁻¹ * g⁻¹ * β).1 := rfl
  have inj : Function.Injective (S.subtype.mapMatrix (m := Fin n)) := Matrix.map_injective Subtype.val_injective
  refine ⟨⟨a, b, inj ?_, inj ?_⟩, ?_⟩
  · rw [map_mul, ha, hb, map_one, ← Units.val_mul, ← Units.val_one]
    congr 1
    group
  · rw [map_mul, ha, hb, map_one, ← Units.val_mul, ← Units.val_one]
    congr 1
    group
  · change β.1 * S.subtype.mapMatrix a * (β⁻¹).1 = _
    rw [ha, ← Units.val_mul, ← Units.val_mul]
    congr 1
    group

theorem entry_mem_of_keeps {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (e : A ≃+* B) (S : Subring B) (β : GL (Fin n) B)
    {P : AddSubgroup (Fin n → A)} (hP : ∀ z, z ∈ P ↔ ∀ i, ((β⁻¹).val *ᵥ fun i => e (z i)) i ∈ S)
    (m : Matrix (Fin n) (Fin n) A) (hm : ∀ z ∈ P, m *ᵥ z ∈ P) (i j : Fin n) : ((β⁻¹).1 * m.map e * β.1) i j ∈ S := by
  have h1 : (fun a => e.symm (β.1 a j)) ∈ P := by
    rw [hP]
    intro a
    simp only [RingEquiv.apply_symm_apply]
    have : ((β⁻¹).1 *ᵥ fun a => β.1 a j) a = ((β⁻¹).1 * β.1) a j := rfl
    rw [this, Units.inv_mul, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have h2 := (hP _).1 (hm _ h1) i
  rw [equiv_mulVec] at h2
  simp only [RingEquiv.apply_symm_apply] at h2
  rw [Matrix.mulVec_mulVec] at h2
  exact h2

theorem exists_ker_of_closure {A B K : Type} [CommRing A] [CommRing B] [CommRing K] (S : Subring B) (f : A →+* B) (ρ : S →+* K)
    {s : Set A} (h : ∀ z ∈ s, ∃ Z : S, (Z : B) = f z ∧ ρ Z = 0) (U a : S) (u a' : A) (hu : f u = U) (ha : f a' = a)
    (hz : u - a' ∈ AddSubgroup.closure s) : ρ U = ρ a := by
  have key : ∀ z ∈ AddSubgroup.closure s, ∃ Z : S, (Z : B) = f z ∧ ρ Z = 0 := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz => exact h z hz
    | zero => exact ⟨0, (map_zero _).symm, map_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨X, h1, h2⟩ := hx
      obtain ⟨Y, h3, h4⟩ := hy
      exact ⟨X + Y, by rw [map_add, ← h1, ← h3]; rfl, by rw [map_add, h2, h4, add_zero]⟩
    | neg x _ hx =>
      obtain ⟨X, h1, h2⟩ := hx
      exact ⟨-X, by rw [map_neg, ← h1]; rfl, by rw [map_neg, h2, neg_zero]⟩
  obtain ⟨Z, h1, h2⟩ := key _ hz
  have : Z = U - a := Subtype.ext (by rw [h1, map_sub, hu, ha]; rfl)
  rwa [this, map_sub, sub_eq_zero] at h2

theorem exists_tmul_res {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (P : Pl E) {c : 𝓞 E}
    (hc : c ∈ P.asIdeal) {α : Formalism.L2.Herm.Af F} (hα : ∀ v, α v ∈ v.adicCompletionIntegers F) :
    ∃ Z : Formalism.L2.Herm.intAf F E, (Z : E ⊗[F] Formalism.L2.Herm.Af F) = (c : E) ⊗ₜ α ∧ resS F P Z = 0 := by
  refine ⟨oToS _ _ c * ⟨(1 : E) ⊗ₜ α, GlobalTheory.PlaceDatum.tmul_mem_int ⟨1, map_one _⟩ hα⟩, ?_, ?_⟩
  · change ((c : E) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) * ((1 : E) ⊗ₜ α) = (c : E) ⊗ₜ α
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  · rw [map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hc, zero_mul]

theorem mulVec_inv_mem {A : Type} [CommRing A] {n : ℕ} {P : Set (Fin n → A)} (g : GL (Fin n) A) (h : g.1.mulVec '' P = P) :
    (∀ z ∈ P, g.1 *ᵥ z ∈ P) ∧ ∀ z ∈ P, (g⁻¹).1 *ᵥ z ∈ P := by
  refine ⟨fun z hz => h ▸ ⟨z, hz, rfl⟩, fun z hz => ?_⟩
  obtain ⟨z', hz', rfl⟩ := h.ge hz
  rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

theorem exists_frame_matrix {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (h : IsSDFrame V β Λ 1) {u : GA D V}
    (hu : L2.Pj.gLat V u = latHat V) : ∃ y, frGL β y = Lev.finE V u := by
  obtain ⟨k1, k2⟩ := mulVec_inv_mem (finHom V u) hu
  obtain ⟨y, hy⟩ := exists_unit_of_mem (SI D) β (Lev.finE V u)
    (entry_mem_of_keeps (sw D) (SI D) β (mem_latHat_iff h) _ k1)
    (entry_mem_of_keeps (sw D) (SI D) β (mem_latHat_iff h) _ k2)
  exact ⟨y, Units.ext hy⟩

theorem resS_eq_of_sub_mem (P : Pl D.host.E) {I : Ideal (𝓞 D.host.E)} (hI : I ≤ P.asIdeal) (U : SI D) (a : 𝓞 D.host.E)
    (h : unswap D U - 1 ⊗ₜ (a : D.host.E) ∈ GlobalTheory.AdLat.hat1 D.host.F (algebraMap (𝓞 D.host.E) D.host.E '' (I : Set (𝓞 D.host.E)))) :
    resS D.host.F P U = Ideal.Quotient.mk _ a := by
  refine (exists_ker_of_closure (SI D) (Lev.swapAE D) (resS D.host.F P) ?_ U (oToS _ _ a) _ _ (swap_unswap _) rfl h).trans
    (resS_oToS P a)
  rintro _ ⟨α, hα, _, ⟨c, hc, rfl⟩, rfl⟩
  exact exists_tmul_res P (hI hc) hα

theorem unswap_det {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {u : GA D V} {y : GL (Fin V.rank) (SI D)}
    (hy : frGL β y = Lev.finE V u) : unswap D (y.1.det : SI D) = (finHom V u).1.det := by
  have h2 : Lev.swapAE D (finHom V u).1.det = (Lev.finE V u).1.det := (Lev.swapAE D).map_det _
  rw [← det_frGL β y, hy, ← h2, unswap_swap]

set_option maxHeartbeats 1600000 in

theorem exists_root_value {T0 : Type} {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) (t : T0) {V : HSp D}
    {u : GA D V} (hu : u ∈ GfC V)
    (U : Formalism.L2.Herm.intAf D.host.F D.host.E) (hU : unswap D U = (finHom V u).1.det) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (l : Level H)
    (hQ : ∀ P ∈ L.Q t, l.Mb ≤ P.asIdeal) (v : ∀ P : L.Q t, (kP P.1)ˣ)
    (hv : ∀ P : L.Q t, (v P : kP P.1) = resS D.host.F P.1 U) :
    ∃ x, IsDetRoot V u x ∧ ((L.xi t x : Circle) : ℂ) = ∏ P : L.Q t, ((L.xiR t P.1 (v P) : ℂˣ) : ℂ) := by
  have hM : (l.M : 𝓞 D.host.E) ∈ l.Mb := Ideal.mul_le_left (l.prod.ge (Ideal.mem_span_singleton_self _))
  have hMb : l.Mb ≠ 0 := fun e => by
    rw [e, Ideal.zero_eq_bot, Ideal.mem_bot, Nat.cast_eq_zero] at hM
    have := l.three_le
    omega
  obtain ⟨a, b, s, s', hb, hs, hs', hin, -⟩ := exists_half_elements l (Ideal.finite_factors hMb).toFinset fun P => by
    rw [Set.Finite.mem_toFinset]
    exact Ideal.dvd_iff_le
  replace hin : ∀ P ∈ L.Q t, a ∈ P.asIdeal ∧ (l.M : 𝓞 D.host.E) ∈ P.asIdeal := fun P hP =>
    hin P ((Set.Finite.mem_toFinset _).2 (Ideal.dvd_iff_le.2 (hQ P hP)))
  generalize l.M = m at hs hs' hin
  obtain ⟨z, z', hz, hz', hzz, hroot, p, hp, hzp⟩ := exists_root_half m U a b s s' hb hs hs'
    (by rw [hU]; exact GlobalTheory.RecDict.det_finHom_norm V u)
  obtain ⟨x, hx1, hx2, hx3⟩ := GlobalTheory.DetRootCong.exists_idele D z z' hzz
  refine ⟨x, isDetRoot_of_fin hu hx1 (by rw [hx2, ← hU]; exact hroot), ?_⟩
  let p' : Formalism.L2.Herm.intAf D.host.F D.host.E := ⟨Lev.swapAE D p, swap_int hp⟩
  refine char_finUnit (hL.xi t) (hL.xi_tame t) (L.Q t) (L.xiR t) (hL.xiR t) ⟨hx1, hx2 ▸ hz, hx3 ▸ hz'⟩
    (oToS _ _ a + oToS _ _ b * U + oToS _ _ m * p') ?_ _ (fun P => ?_) fun P hP => ?_
  · rw [hx2, hzp, ← unswap_swap p]
    exact map_coe_sum _ (unswap D) _ _ U _ p' m (map_natCast _ m)
  · exact (hv P).trans (resS_sum_left P.1 U p' hs (hin P.1 P.2).2 (hin P.1 P.2).1).symm
  · by_cases hun : (L.xiH t).UnrAt P
    · exact Or.inl hun
    obtain ⟨P', hP', hc⟩ := ((hL.Q_ram t P).1 hun).resolve_left hP
    obtain ⟨b', hb', eb⟩ := hc a (hin P' hP').1
    obtain ⟨m', hm', em⟩ := hc _ (hin P' hP').2
    obtain rfl : b' = b := RingOfIntegers.ext (eb.trans hb.symm)
    obtain rfl : m' = (m : 𝓞 D.host.E) := RingOfIntegers.ext (by
      rw [em]
      change star ((m : 𝓞 D.host.E) : D.host.E) = ((m : 𝓞 D.host.E) : D.host.E)
      rw [show ((m : 𝓞 D.host.E) : D.host.E) = (m : D.host.E) from
        map_natCast (algebraMap (𝓞 D.host.E) D.host.E) m, star_natCast])
    exact Or.inr (resS_sum_right P U p' hs hm' hb')

section Pairing

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem natCast_mem (l : Level H) : (l.M : 𝓞 E) ∈ l.Mb ∧ (l.M : 𝓞 E) ∈ Mfr l :=
  ⟨Ideal.mul_le_left (l.prod.ge (Ideal.mem_span_singleton_self _)),
    Ideal.mul_le_right (l.prod.ge (Ideal.mem_span_singleton_self _))⟩

theorem cSep_sub_one (l : Level H) : cSep l - 1 ∈ l.Mb := by
  obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 (l.coprime.ge (Submodule.mem_top (x := (1 : 𝓞 E))))
  have h : ∃ c, c ∈ Mfr l ∧ c - 1 ∈ l.Mb := ⟨b, hb, by rw [← e, sub_add_cancel_right]; exact neg_mem ha⟩
  unfold cSep
  rw [dif_pos h]
  exact h.choose_spec.2

theorem sub_mem_of_pairing (l : Level H) (f : Dw.La →ₗ[𝓞 E] Dw.La) (hf : ∀ a b, (l.M : ℤ) ∣ Dw.EF (f a) (f b) - Dw.EF a b)
    (hs : ∀ b, ∃ b', f b' - b ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La)) (a z : Dw.La)
    (h : ∀ b, (l.M : ℤ) ∣ Dw.EF z (cSep l • f b) - Dw.EF a (cSep l • b)) :
    f a - z ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La) := by
  have h1 : H.bar (cSep l) • (f a - z) ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La) := by
    refine mem_of_modN Dw (natCast_mem l).2 (modN_of_dvd Dw (by have := l.three_le; omega) fun b => ?_)
    obtain ⟨b', hb'⟩ := hs b
    have h2 := dvd_right Dw l.prod (cSep_mem l) (f a - z) hb'
    have h3 := dvd_sub (dvd_sub (hf a (cSep l • b')) (h b')) h2
    rw [Dw.adj, bar_bar]
    simp only [map_smul f, smul_sub, map_sub, LinearMap.sub_apply] at h3 ⊢
    exact h3.imp fun t ht => by linear_combination ht
  have h2 : H.bar (cSep l - 1) • (f a - z) ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La) :=
    Submodule.smul_mem_smul (Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) (cSep_sub_one l)) trivial
  have := sub_mem h1 h2
  rwa [map_sub, map_one, sub_smul, one_smul, sub_sub_cancel] at this

theorem exists_isometry_of_adjoint {l l₂ : Level H} (hM : l.M ∣ l₂.M) (hb : l₂.Mb ≤ l.Mb)
    (σq : LevQ Dw l₂ ≃ₗ[𝓞 E] LevQ Dw l₂) (σc : LevQc Dw l₂ ≃ₗ[𝓞 E] LevQc Dw l₂)
    (h1 : ∀ a b : Dw.La, σq (Submodule.Quotient.mk a) = Submodule.Quotient.mk b →
      a - b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La))
    (h2 : ∀ (x : LevQc Dw l₂) (q : LevQ Dw l₂),
      (l₂.M : ℤ) ∣ Dw.EF (qRep (σc x)) (cSep l₂ • levRep (σq q)) - Dw.EF (qRep x) (cSep l₂ • levRep q)) :
    ∃ s : Sim Dw, (∀ n, s.ν n = 1) ∧ (∀ a, σq (Submodule.Quotient.mk a) = Submodule.Quotient.mk (s.f l₂.M a)) ∧
      (∀ a, σc (Submodule.Quotient.mk a) = Submodule.Quotient.mk (s.f l₂.M a)) ∧
      ∀ a, s.f l₂.M a - a ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La) := by
  obtain ⟨s, hν, hs, -⟩ := GlobalTheory.LevelIsometry.exists_isometry_inducing E H Dw l₂ σq
  have hs' : ∀ a, σq (Submodule.Quotient.mk a) = Submodule.Quotient.mk (s.f l₂.M a) := fun a => (hs a).symm
  have hM₂ : 0 < l₂.M := by have := l₂.three_le; omega
  have hf : ∀ a b, (l₂.M : ℤ) ∣ Dw.EF (s.f l₂.M a) (s.f l₂.M b) - Dw.EF a b := fun a b => by
    have := s.mult _ hM₂ a b
    rwa [hν, one_mul] at this
  obtain ⟨g, hg⟩ := s.inv _ hM₂
  have hsurj : ∀ b, ∃ b', s.f l₂.M b' - b ∈ (l₂.Mb • ⊤ : Submodule (𝓞 E) Dw.La) := fun b =>
    ⟨g b, mem_of_modN Dw (natCast_mem l₂).1 (hg b).2⟩
  refine ⟨s, hν, hs', fun a => ?_, fun a => ?_⟩
  · rw [← qRep_spec (σc _), eq_comm, Submodule.Quotient.eq]
    refine sub_mem_of_pairing l₂ _ hf hsurj a _ fun b => ?_
    have e1 := h2 (Submodule.Quotient.mk a) (Submodule.Quotient.mk b)
    have e2 := dvd_right Dw l₂.prod (cSep_mem l₂) (qRep (σc (Submodule.Quotient.mk a)))
      ((Submodule.Quotient.eq _).1 ((levRep_spec _).trans (hs' b)))
    have e3 := dvd_right Dw l₂.prod (cSep_mem l₂) (qRep (Submodule.Quotient.mk a : LevQc Dw l₂))
      ((Submodule.Quotient.eq _).1 (levRep_spec (Submodule.Quotient.mk b : LevQ Dw l₂)))
    have e4 := dvd_left Dw l₂.prod (cSep_mem l₂) b
      ((Submodule.Quotient.eq _).1 (qRep_spec (Submodule.Quotient.mk a : LevQc Dw l₂)))
    have e5 := dvd_add (dvd_add (dvd_sub e1 e2) e3) e4
    simp only [smul_sub, map_sub, LinearMap.sub_apply] at e5
    exact e5.imp fun t ht => by linear_combination ht
  · refine sub_mem_of_pairing l _ (fun a b => (Int.natCast_dvd_natCast.2 hM).trans (hf a b))
      (fun b => (hsurj b).imp fun b' h => Submodule.smul_mono hb le_rfl h) a a fun b => ?_
    have := dvd_right Dw l.prod (cSep_mem l) a (neg_mem (h1 b _ (hs' b)))
    rwa [neg_sub, smul_sub, map_sub] at this

end Pairing

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

theorem exists_finite_of_isometry {V : HSp D} {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)}
    (hι : GlobalTheory.Member.IotaOK Dw V ι) (s : Sim Dw) (hν : ∀ n, s.ν n = 1) :
    ∃ u ∈ GfC V, L2.Pj.gLat V u = latHat V ∧ ∀ N : ℕ, 0 < N → ∀ a, ∃ w ∈ latGHat V 1,
      (finHom V u).1.mulVec (finVec V (ι a)) = finVec V (ι (s.f N a)) + N • w := by
  obtain ⟨κ, hκ, hκs⟩ := GlobalTheory.ShortMove.exists_adelic_of_isometry D V H Dw ι hι.emb hι.isom s hν
  obtain ⟨b, hb, u, hu, e⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 κ
  have hb' : finHom V b = 1 := hb
  have hf : finHom V u = finHom V κ := by rw [e, map_mul, hb', one_mul]
  obtain ⟨-, m2, -, m4⟩ := GlobalTheory.Member.latG_move D V
  have hL : latG V 1 = latG V u := GlobalTheory.Member.LatMove.lat_eq_of_hat_eq V (hκ.symm.trans (m2 u κ hf).2.symm)
  have hc := m4 1 u hL
  rw [inv_one, one_mul] at hc
  exact ⟨u, hu, GlobalTheory.MarkDet.gLat_eq_of_finCong hc, hf ▸ hκs⟩

theorem latGHat_one_eq {V : HSp D} {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) :
    latGHat V 1 = GlobalTheory.AdLat.hat D.host.F (Set.range ι) := by
  rw [(GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).2.2.2.2.1, ← hι.2, LinearMap.coe_range]

set_option maxHeartbeats 1000000 in

theorem factor_det_eq {V : HSp D} {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι)
    {I J : Ideal (𝓞 D.host.E)} (hIJ : IsCoprime I J) {M : ℕ} (hM : (M : 𝓞 D.host.E) ∈ I)
    (e : (Dw.La ⧸ (I • ⊤ : Submodule (𝓞 D.host.E) Dw.La)) ≃ₗ[𝓞 D.host.E] (Fin V.rank → 𝓞 D.host.E ⧸ I))
    (k : (Dw.La ⧸ (I • ⊤ : Submodule (𝓞 D.host.E) Dw.La)) ≃ₗ[𝓞 D.host.E] (Dw.La ⧸ (I • ⊤ : Submodule (𝓞 D.host.E) Dw.La)))
    (δ : 𝓞 D.host.E ⧸ I) (hδ : ∀ a : Matrix (Fin V.rank) (Fin V.rank) (𝓞 D.host.E),
      (∀ j, k (e.symm (Pi.single j 1)) = ∑ i, a i j • e.symm (Pi.single i 1)) → δ = Ideal.Quotient.mk I a.det)
    {u : GA D V} {f : Dw.La →ₗ[𝓞 D.host.E] Dw.La}
    (h : ∀ a ∈ J • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat V 1,
      (finHom V u).1.mulVec (finVec V (ι a)) - finVec V (ι (f a)) = M • w)
    (hk : ∀ a, Submodule.Quotient.mk (f a) = k (Submodule.Quotient.mk a))
    (U : Formalism.L2.Herm.intAf D.host.F D.host.E) (hU : unswap D U = (finHom V u).1.det) (P : Pl D.host.E) (hP : I ≤ P.asIdeal) :
    Ideal.Quotient.factor hP δ = resS D.host.F P U := by
  have := Dw.fin
  obtain ⟨v, hv₁, hv₂, hv₃⟩ := GlobalTheory.TwistTie.exists_basis_lift I J hIJ e
  have hrange : (latG V 1 : Set (Fin V.rank → D.host.E)) = Set.range ι := by
    rw [← hι.2, LinearMap.coe_range]
  obtain ⟨a, ha₁, ha₂⟩ := GlobalTheory.TwistTie.det_sub_mem_hat D.host.F ι (hrange ▸ (GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).2.1) I
    (fun e => P.isPrime.ne_top (top_le_iff.1 (e ▸ hP))) v hv₃ f M hM (finHom V u).1
    (by rw [← GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers, ← hU]; exact unswap_int U)
    (fun j => by
      rw [← latGHat_one_eq hι]
      exact h _ (hv₁ j))
  have hdet := hδ a fun j => by
    rw [← hv₂, ← hk, (Submodule.Quotient.eq _).2 (ha₁ j), ← Submodule.mkQ_apply, map_sum]
    simp only [map_smul, Submodule.mkQ_apply, hv₂]
  rw [hdet, Ideal.Quotient.factor_mk]
  exact (resS_eq_of_sub_mem P hP U _ (by rw [hU]; exact ha₂)).symm

theorem exists_lift_char {Γ : Type} [Group Γ] (K : IntermediateField ℚ ℂ) (χ : Γ →* ℂˣ) (h : ∀ g, (χ g : ℂ) ∈ K) :
    ∃ ψ : Γ →* Kˣ, ∀ g, (((ψ g : Kˣ) : K) : ℂ) = χ g :=
  ⟨MonoidHom.mk' (fun g => Units.mk0 ⟨_, h g⟩ fun e => (χ g).ne_zero (congrArg Subtype.val e)) fun g g' =>
    Units.ext (Subtype.ext (by simp)), fun _ => rfl⟩

theorem conj_mem {l : Level H} {P : Pl D.host.E} (hP : l.Mb ≤ P.asIdeal) :
    ∀ a ∈ Mfr l, ∃ a' ∈ P.asIdeal, (a' : D.host.E) = star (a : D.host.E) := fun a ha =>
  ⟨H.bar a, hP (bar_mem ha), H.bar_eq a⟩

theorem omegaK_congr {a b : ℕ} {Pg : Finset (Pl D.host.E)} {y y' : ∀ P : Pl D.host.E, Matrix (Fin b) (Fin a) (kP P)}
    (h : ∀ P ∈ Pg, y P = y' P) : omegaK Pg y = omegaK Pg y' := by
  have : (∀ P ∈ Pg, LowZero a (y P) ∧ topL a (y P) = 1) ↔ ∀ P ∈ Pg, LowZero a (y' P) ∧ topL a (y' P) = 1 :=
    forall₂_congr fun P hP => by rw [h P hP]
  unfold omegaK
  exact @if_congr _ _ _ (_) (_) _ _ _ _ this rfl rfl

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m} {t : T0}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

set_option maxHeartbeats 1600000 in

theorem datum_move {l₂ : Level H} {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)} (hι : LatEmb (Wc D i) ι)
    {K' : Type} [Field K'] {σ' : K' →+* ℂ} {φ : (Fin (Vc D i).rank → LevQc Dw l₂) → K'}
    (hφ : PhiIs R i σ' t ι (Mfr l₂ • ⊤) φ) (hPg : ∀ P ∈ R.Pg, l.Mb ≤ P.asIdeal) (hQ : ∀ P ∈ R.Q t, l₂.Mb ≤ P.asIdeal)
    {u : GA D (Wc D i)} {y : GL (Fin (Wc D i).rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)}
    (hy : frGL (R.βW i) y = Lev.finE (Wc D i) u) {f : Dw.La →ₗ[𝓞 D.host.E] Dw.La}
    (hf : ∀ a, ∃ w ∈ latGHat (Wc D i) 1,
      (finHom (Wc D i) u).1.mulVec (finVec (Wc D i) (ι a)) = finVec (Wc D i) (ι (f a)) + l₂.M • w)
    (hf' : ∀ a, f a - a ∈ (Mfr l • ⊤ : Submodule (𝓞 D.host.E) Dw.La)) (v : ∀ P : R.Q t, (kP P.1)ˣ)
    (hv : ∀ P : R.Q t, (v P : kP P.1) = resS D.host.F P.1 y.1.det) (x : Fin (Vc D i).rank → Dw.La) :
    σ' (φ fun b => Submodule.Quotient.mk (x b)) = ((∏ P : R.Q t, R.xiR t P.1 (v P) : ℂˣ) : ℂ)⁻¹ *
      σ' (φ fun b => Submodule.Quotient.mk (f (x b))) := by
  obtain ⟨e, -, he⟩ := hφ
  have hint := fun x => (he x).1
  rw [latGHat_one_eq hι] at hf
  have h1 := GlobalTheory.TwistDatumRight.omegaQ_mul_right D _ _ (R.Q t) (R.xiR t)
    (fun P => Matrix.GeneralLinearGroup.map (resS D.host.F P) y) _ _ fun P hP =>
      GlobalTheory.AdjMove.redM_uMat_move D _ _ _ _ e _ ι hint u y hy l₂.M P (hQ P hP (natCast_mem l₂).1) (fun b => f (x b)) x
        fun b => hf (x b)
  have h2 : omegaK R.Pg (fun PP => redM PP (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (x b))) =
      omegaK R.Pg (fun PP => redM PP (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (f (x b)))) :=
    omegaK_congr fun P hP =>
      GlobalTheory.redM_adj_congr D _ _ _ _ e _ ι hint (Mfr l) P (conj_mem (hPg P hP)) (fun b => f (x b)) x fun b => hf' (x b)
  have h3 : ∏ P ∈ R.Q t, R.xiR t P (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (resS D.host.F P) y)) =
      ∏ P : R.Q t, R.xiR t P.1 (v P) := by
    rw [← Finset.prod_coe_sort]
    refine Finset.prod_congr rfl fun P _ => congrArg _ (Units.ext ?_)
    rw [hv, RingHom.map_det]
    rfl
  rw [(he x).2, (he fun b => f (x b)).2, h1, h2, h3, mul_left_comm]

set_option maxHeartbeats 1600000 in

theorem exists_char {μ0 : T0} (hL : R.toLevCh.Is μ0) (d : DeltaDat Xo c (Vc D i).rank) (hd : d.IsLev)
    {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)} (hι : GlobalTheory.Member.IotaOK Dw (Wc D i) ι)
    (hr : Dw.p + Dw.q = (Wc D i).rank) (hpq : 1 ≤ Dw.p + Dw.q) (hh : HalfIs R t l.Mb d.I)
    (hmem : ∀ P ∈ R.Q t, ∀ x, ((R.xiR t P x : ℂˣ) : ℂ) ∈ c.F)
    {xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ} (hxi : XiIs R i t xi)
    {φ : (Fin (Vc D i).rank → LevQc Dw d.l₂) → c.F} (hφ : PhiIs R i c.F.val.toRingHom t ι (Mfr d.l₂ • ⊤) φ) :
    ∃ ψ : (LaI Xo c d ≃ₗ[𝓞 D.host.E] LaI Xo c d) →* c.Fˣ,
      (∀ (k : LaI Xo c d ≃ₗ[𝓞 D.host.E] LaI Xo c d) (s : Sim Dw),
        (∀ a : Dw.La, (Submodule.Quotient.mk (s.f d.l₂.M a) : LaI Xo c d) = k (Submodule.Quotient.mk a)) →
        ∃ u : GA D (Wc D i), latGHat (Wc D i) u = latGHat (Wc D i) 1 ∧
          (∀ a ∈ Mfr d.l₂ • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat (Wc D i) 1,
            (finHom (Wc D i) u).1.mulVec (finVec (Wc D i) (ι a)) = finVec (Wc D i) (ι (s.f d.l₂.M a)) + d.l₂.M • w) ∧
          (((ψ k : c.Fˣ) : c.F) : ℂ) = (xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) u)) : ℂˣ)) ∧
      ∀ w : (Fin (Vc D i).rank → LevQ Dw d.l₂) → c.F, (∀ q, d.eF (w q) = phiHat d.c₂ (fun x => d.eF (φ x)) q) →
        GlobalTheory.ClsVal.DatEq d ψ w := by
  have hd' := hd
  obtain ⟨-, hM, hcop, hMb, hI, -⟩ := hd'
  have hM₂ : 0 < d.l₂.M := by have := d.l₂.three_le; omega
  have hpd : d.pd ≠ 0 := fun e => by rw [hM, e] at hM₂; omega
  have hpI : (d.pd : 𝓞 D.host.E) ∈ d.I := GlobalTheory.CharacterFunction.natCast_mem_half hM hMb
  have hI0 : d.I ≠ ⊥ := fun e => hpd (by rw [e, Ideal.mem_bot] at hpI; exact_mod_cast hpI)
  have : Finite (𝓞 D.host.E ⧸ d.I) := Ideal.finiteQuotientOfFreeOfNeBot _ hI0
  have := Dw.fin
  have := Dw.proj
  obtain ⟨e⟩ := HalfPairing.nonempty_equiv_quot (N := Dw.La) d.I (Wc D i).rank (Dw.rank.trans hr)
  obtain ⟨δ, -, hδ⟩ := GlobalTheory.TwistTie.exists_det_hom d.I (hr ▸ hpq) e
  have hbI : d.l₂.Mb ≤ d.I := hMb ▸ Ideal.mul_le_right
  have hbM : d.l₂.Mb ≤ l.Mb := hMb ▸ Ideal.mul_le_left
  have hQ : ∀ P ∈ R.Q t, d.l₂.Mb ≤ P.asIdeal := fun P hP => hbI.trans (hh.2.1 P hP)
  have hPg : ∀ P ∈ R.Pg, l.Mb ≤ P.asIdeal := fun P hP => by
    rw [hh.1]
    exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hP)
  have hIJ : IsCoprime d.I (Mfr d.l₂) := by
    rw [Mfr, hMb, Ideal.map_mul]
    refine IsCoprime.mul_right ?_ (Ideal.isCoprime_iff_sup_eq.2 hI)
    obtain ⟨α, β, hαβ⟩ := Nat.Coprime.cast (R := 𝓞 D.host.E) hcop
    exact Ideal.isCoprime_iff_exists.2 ⟨_, Ideal.mul_mem_left _ α hpI, _, Ideal.mul_mem_left _ β (natCast_mem l).2, hαβ⟩
  let v : ∀ P : R.Q t, (LaI Xo c d ≃ₗ[𝓞 D.host.E] LaI Xo c d) →* (kP P.1)ˣ := fun P =>
    (Units.map (Ideal.Quotient.factor (hh.2.1 P.1 P.2)).toMonoidHom).comp δ
  obtain ⟨ψ, hψ⟩ := exists_lift_char c.F (∏ P : R.Q t, (R.xiR t P.1).comp (v P)) fun k => by
    rw [MonoidHom.finsetProd_apply, Units.coe_prod]
    exact prod_mem fun P _ => hmem P.1 P.2 _
  simp only [MonoidHom.finsetProd_apply, MonoidHom.comp_apply] at hψ
  have hv : ∀ (k : LaI Xo c d ≃ₗ[𝓞 D.host.E] LaI Xo c d) (u : GA D (Wc D i)) (f : Dw.La →ₗ[𝓞 D.host.E] Dw.La),
      (∀ a ∈ Mfr d.l₂ • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat (Wc D i) 1,
        (finHom (Wc D i) u).1.mulVec (finVec (Wc D i) (ι a)) - finVec (Wc D i) (ι (f a)) = d.l₂.M • w) →
      (∀ a, Submodule.Quotient.mk (f a) = k (Submodule.Quotient.mk a)) → ∀ y, frGL (R.βW i) y = Lev.finE (Wc D i) u →
      ∀ P : R.Q t, (v P k : kP P.1) = resS D.host.F P.1 y.1.det := fun k u f h hk y hy P =>
    factor_det_eq hι.emb hIJ (hbI (natCast_mem d.l₂).1) e k _ (hδ k) h hk _ (unswap_det hy) P.1 (hh.2.1 P.1 P.2)
  refine ⟨ψ, fun k s hk => ?_, fun w hw => GlobalTheory.ClsVal.datEq_of_phiHat _ H Dw l Xo c _ d hd ψ φ w hw
    fun k σq σc h1 h2 x => ?_⟩
  · obtain ⟨g', hg'⟩ := s.inv d.l₂.M hM₂
    obtain ⟨u, hu, hu', hlift⟩ := GlobalTheory.HalfLift.exists_unitary_inducing D H Dw d.l₂ _ ι hι (s.f d.l₂.M) g' fun a =>
      ⟨mem_of_modN Dw (natCast_mem d.l₂).1 (hg' a).1, mem_of_modN Dw (natCast_mem d.l₂).1 (hg' a).2⟩
    obtain ⟨y, hy⟩ := exists_frame_matrix (hL.βW i) hu'
    obtain ⟨x, hx, hx'⟩ := exists_root_value hL t hu _ (unswap_det hy) d.l₂ hQ _ (hv k u _ hlift hk y hy)
    refine ⟨u, by unfold latGHat; rw [hu', GlobalTheory.TwistTie.gLat_one], fun a ha => ?_, ?_⟩
    · obtain ⟨w, hw, ew⟩ := hlift a ha
      exact ⟨w, hw, sub_eq_iff_eq_add'.1 ew⟩
    · rw [hψ, hxi u x hx, Units.coe_prod]
      exact hx'.symm
  · obtain ⟨s, hν, s1, s2, s3⟩ := exists_isometry_of_adjoint (hM ▸ Dvd.intro _ rfl) hbM σq σc (fun a b h => (h1 a b h).1) h2
    obtain ⟨u, -, hu', hf⟩ := exists_finite_of_isometry hι s hν
    obtain ⟨y, hy⟩ := exists_frame_matrix (hL.βW i) hu'
    have key := datum_move hι.emb hφ hPg hQ hy (hf _ hM₂) s3 _ (hv k u _ (fun a _ => (hf _ hM₂ a).imp fun w hw =>
      ⟨hw.1, sub_eq_iff_eq_add'.2 hw.2⟩) (fun a => (h1 a _ (s1 a)).2.symm) y hy) fun b => qRep (σc.symm (x b))
    simp only [← s2, qRep_spec, LinearEquiv.apply_symm_apply] at key
    apply c.F.val.toRingHom.injective
    rw [key, map_mul, ← hψ, Units.val_inv_eq_inv_val, map_inv₀]
    rfl

theorem xi_laws {μ0 : T0} (hL : R.toLevCh.Is μ0) {xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ} (hxi : XiIs R i t xi) :
    (∀ γ ∈ GQ (Wc D i), xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) γ)) = 1) ∧
      ∃ n, 0 < n ∧ ∀ g : GA D (Wc D i), xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g)) ^ n = 1 := by
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  obtain ⟨xi', h1, -, h3, h4⟩ := GlobalTheory.TupleCover.exists_xi D (Wc D i) (R.xi t) (R.xiH t) (hL.xi t) n hn ho (hL.xi_triv t)
    (hL.xi_tame t)
  have e : ∀ g : GA D (Wc D i), xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g)) =
      xi' (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g)) := fun g => by
    obtain ⟨x, hx⟩ := (GlobalTheory.Member.isDetRoot_laws D (Wc D i)).1 g
    exact Units.ext ((hxi g x hx).trans (h1 g x hx).symm)
  exact ⟨fun γ hγ => (e γ).trans (h3 γ hγ), n, hn, fun g => by rw [e, h4]⟩

set_option maxHeartbeats 1000000 in

theorem psiTie_of_values (V : HSp D) {n r : ℕ} (d : DeltaDat Xo c n) (hr : V.rank = r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hι : GlobalTheory.Member.IotaOK Dw V ι) (hpq : 1 ≤ Dw.p + Dw.q)
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (hx₀ : ∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 →
      ReciprocityTheory.ChartRestriction.G.FD.gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) (x₀ τ) =
        Matrix.diagonal fun a : Fin r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn Dw.q (a : ℕ) : ℝ) : ℂ))
    (hd : d.IsLev) (hA : d.l₂.A = 1) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (N : ℕ) (hN : 0 < N)
    (hxN : ∀ h : GA D V, xi (Matrix.GeneralLinearGroup.det (finHom V h)) ^ N = 1)
    (hxi : ∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V γ)) = 1) (U₂ : _) (dict₂ : _) (c0 : ℂ) (hc0 : c0 ^ N = 1)
    (hv : GlobalTheory.OneMapAll.CXiAt V hr c.F.val.toRingHom d U₂ dict₂ ι x₀ xi c0)
    (ψ : (LaI Xo c d ≃ₗ[𝓞 D.host.E] LaI Xo c d) →* c.Fˣ)
    (hψ : ∀ (k : LaI Xo c d ≃ₗ[𝓞 D.host.E] LaI Xo c d) (s : Sim Dw),
      (∀ a : Dw.La, (Submodule.Quotient.mk (s.f d.l₂.M a) : LaI Xo c d) = k (Submodule.Quotient.mk a)) →
      ∃ u : GA D V, latGHat V u = latGHat V 1 ∧
        (∀ a ∈ Mfr d.l₂ • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat V 1,
          (finHom V u).1.mulVec (finVec V (ι a)) = finVec V (ι (s.f d.l₂.M a)) + d.l₂.M • w) ∧
        (((ψ k : c.Fˣ) : c.F) : ℂ) = (xi (Matrix.GeneralLinearGroup.det (finHom V u)) : ℂˣ)) : d.PsiTie ψ := by
  subst hr
  obtain ⟨hU, hW, g₀, e₀, F, ik, φ, th, hth, hD, hval⟩ := hv
  intro k g ρ _ _ hρ hk K _ _ _ y y' hy
  obtain ⟨u, h1, h2, h3⟩ := hψ k g hk
  refine GlobalTheory.TwistTie.value_ratio V U₂ dict₂ ι e₀ F ik φ th x₀ (RingHom.ext fun _ => rfl) hA hpq hU hW hD hι hth
    (fun k τ hτ => ?_) d.cδ hd.2.2.2.2.2.2.2.1 c0 xi N hN hc0 hxN hval hxi g ρ hρ u h1 h2 _ h3 K y y' hy
  rw [(hW k).1, (hU.2.1 k).1]
  exact hx₀ τ (((hU.2.1 k).2 τ).1 hτ)

end GlobalTheory.ClassSumRule

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate

set_option maxHeartbeats 1600000 in

theorem GlobalTheory.ClassSumRule.exists_cusp_isThClsD : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ (t : Tp) (x : O.Cl' t → VsV D i O.c'.F), ∃ f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank, IsThClsD (T.Q.Xo ((i : ℕ) + 1)) O.c' (O.dδ t) (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.vol t) (O.ep t) O.io x f := by
  intro hci D G _ _ Pl0 T0 A T _ R F κ v₀ hR hT i Tp tup O hO t x
  have hj := inR i
  have hσ : GoodEmb T.Q.c O.s0 := rfl
  obtain ⟨-, -, -, -, hr, -, hr1, -, -, -, hDom, -, hLast⟩ := GlobalTheory.AdTh.models_at_record D G Pl0 T0 A T R F κ v₀ hR hT i _ rfl
    (T.dict ((i : ℕ) + 1) T.toCore.σ₀ 1).1
  obtain ⟨hι, hx₀⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T hT.laws _ hj _ hσ (Wc D i) O.hV (rank_Wc i)
  obtain ⟨c0, ⟨m, hm, hc0⟩, hv⟩ := hO.cxi
  obtain ⟨hxi, n, hn, hxn⟩ := GlobalTheory.ClassSumRule.xi_laws hR.lev (hO.tuple t).xi
  obtain ⟨hd, hA, -⟩ := hO.cov t
  have hpq := hr ▸ hr1
  have hN : 0 < m * n := Nat.mul_pos hm hn
  have hcN : c0 ^ (m * n) = 1 := by rw [pow_mul, hc0, one_pow]
  have hxN : ∀ h : GA D (Wc D i), O.xi t (Matrix.GeneralLinearGroup.det (finHom (Wc D i) h)) ^ (m * n) = 1 := fun h => by
    rw [mul_comm, pow_mul, hxn, one_pow]
  obtain ⟨_, _, _, hfam⟩ := hR.fam.tie
  obtain ⟨ψ, hψ, hw⟩ := GlobalTheory.ClassSumRule.exists_char hR.lev (O.dδ t) hd hι (hr.symm.trans (rank_Wc i).symm) hpq
    (hO.tuple t).half (fun P hP z => by
      obtain ⟨a, ha⟩ := GlobalTheory.RationalValues.xiR_mem R hR.lev hR.fam.pl_onto hR.fam.muVal hfam.ok i (tup t) P hP z
      rw [← ha, ← hO.lift.field]
      exact (O.jL a).2) (hO.tuple t).xi (hO.tuple t).phi
  obtain ⟨f, hf, hcls, -⟩ := GlobalTheory.ClsVal.exists_cusp_isThClsD_unique hci _ _ _ _ _ O.c' _ (O.dδ t) _
    (unfBC O.hle (T.U ((i : ℕ) + 1))) hr1
    (fun σ hσ => GlobalTheory.OneMapAll.isUnf_unfExt O.hle σ (fun _ => rfl) (hT.laws.unf _ hj (σ.comp (incF T.Q.c O.c' O.hle)) hσ))
    hT.laws.pins.2.1.2 (fun _ => hO.cov t)
    (GlobalTheory.OneMapTuples.unitC_of_cXiAt D _ _ _ _ _ _ _ _ (O.dδ t) (rank_Wc i) _ hι hpq _ hx₀ hd hA _ _ hN hxN _ _ c0 hcN (hv t))
    ψ (GlobalTheory.ClassSumRule.psiTie_of_values _ (O.dδ t) (rank_Wc i) _ hι hpq _ hx₀ hd hA _ _ hN hxN hxi _ _ c0 hcN (hv t) ψ hψ)
    _ (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.bad t) (O.vol t) (O.ep t) _ O.io (wtA (κ i)) hDom hLast
    (fun k => hw _ (hO.w t k)) (hO.reps t).1 (by
      obtain ⟨-, _, h⟩ := hO.io
      exact h.2.2.1.le) x
  exact ⟨f, hf, hcls⟩

end

end
