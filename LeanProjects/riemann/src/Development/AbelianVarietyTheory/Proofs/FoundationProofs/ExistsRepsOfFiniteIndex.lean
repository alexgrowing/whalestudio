import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPinsRec
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MovedOfSplitPl
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRepSuppSplit
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSplitAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalVAlgebraMapMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitReps

section Abstract

variable {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G)

theorem finite_stab_of_reps {J J' : Subgroup G} (hle : J' ≤ J) {I : Type} {y : I → G} (hy : Bridge.IsReps ι J y)
    (hfin : ∀ i, Finite (Bridge.stab ι J (y i))) (g : G) : Finite (Bridge.stab ι J' g) := by
  obtain ⟨i, ⟨γ, k, rfl⟩, -⟩ := hy g
  have := hfin i
  refine Finite.of_injective (β := Bridge.stab ι J (y i)) (fun δ => ⟨γ⁻¹ * δ.1 * γ, ?_⟩) ?_
  · have h := hle ((Bridge.mem_stab ι).1 δ.2)
    rw [Bridge.mem_stab]
    have := J.mul_mem (J.mul_mem k.2 h) (J.inv_mem k.2)
    convert this using 1
    simp only [map_mul, map_inv]
    group
  · intro a b h
    have h' : γ⁻¹ * a.1 * γ = γ⁻¹ * b.1 * γ := congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h'))

theorem exists_reps_of_finiteIndex {J J' : Subgroup G} (hidx : J'.relIndex J ≠ 0) {I : Type} [Finite I] {y : I → G}
    (hy : Bridge.IsReps ι J y) {X : Type} (f : X → G) (P : X → Prop)
    (hP : ∀ g, ∃ x, P x ∧ ∃ (γ : Γ) (k : J'), g = ι γ * f x * k) :
    ∃ (m : ℕ) (h : Fin m → X), (∀ j, P (h j)) ∧ Bridge.IsReps ι J' fun j => f (h j) := by
  let s : Setoid G := ⟨fun g g' => ∃ (γ : Γ) (k : J'), g = ι γ * g' * k,
    ⟨fun g => ⟨1, 1, by simp⟩, by
      rintro g g' ⟨γ, k, rfl⟩
      exact ⟨γ⁻¹, k⁻¹, by simp [mul_assoc]⟩, by
      rintro g g' g'' ⟨γ, k, rfl⟩ ⟨γ', k', rfl⟩
      exact ⟨γ * γ', k' * k, by simp [mul_assoc]⟩⟩⟩
  have : Finite (J ⧸ J'.subgroupOf J) := Nat.finite_of_card_ne_zero hidx
  have : Finite (Quotient s) := by
    refine Finite.of_surjective (fun p : I × (J ⧸ J'.subgroupOf J) => Quotient.mk s (y p.1 * (p.2.out : J))) ?_
    intro q
    obtain ⟨g, rfl⟩ := Quotient.exists_rep q
    obtain ⟨i, ⟨γ, k, rfl⟩, -⟩ := hy g
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (J'.subgroupOf J) k
    refine ⟨(i, QuotientGroup.mk k), Quotient.sound ⟨γ⁻¹, ⟨(u : J), u.2⟩, ?_⟩⟩
    simp [hu, mul_assoc]
  choose x hx hr using hP
  let e := Finite.equivFin (Quotient s)
  have hq : ∀ q : Quotient s, Quotient.mk s (f (x q.out)) = q := fun q =>
    (Quotient.sound (s := s) (hr q.out)).symm.trans q.out_eq
  refine ⟨_, fun j => x (e.symm j).out, fun j => hx _, fun g => ⟨e (Quotient.mk s g), ?_, fun j hj => ?_⟩⟩
  · refine Quotient.exact (s := s) ?_
    rw [hq, Equiv.symm_apply_apply]
  · have := (Quotient.sound (s := s) hj).trans (hq _)
    rw [this, Equiv.apply_symm_apply]

end Abstract

section Support

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem

variable {D : D7}

theorem suppSplit_mono {F E : Type} [Field F] [Field E] [Algebra F E] [NumberField F] {c : E ≃ₐ[F] E} {n M N : ℕ}
    (hd : M ∣ N) {h : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)} (hs : GlobalTheory.UnRep.SuppSplit c N h) :
    GlobalTheory.UnRep.SuppSplit c M h := by
  obtain ⟨e, h1, h2, h3, h4⟩ := hs
  obtain ⟨u, rfl⟩ := hd
  refine ⟨e, h1, h2, fun v hv => ⟨(h3 v hv).1, fun hm => (h3 v hv).2 ?_⟩, h4⟩
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hm

theorem finCong_mono {V : HSp D} {M N : ℕ} (hd : M ∣ N) {k : GA D V} (hk : GlobalTheory.Member.FinCong V N k) :
    GlobalTheory.Member.FinCong V M k := by
  obtain ⟨u, rfl⟩ := hd
  intro z hz
  obtain ⟨y, hy, e⟩ := hk z hz
  exact ⟨u • y, nsmul_mem hy _, by rw [e, mul_nsmul']⟩

theorem idem_eq_sum (e : Af D.host.F) (he : e * e = e) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (hS : ∀ v, v ∈ S ↔ evalV D.host.F v e ≠ 0) : e = ∑ v ∈ S, singleV D.host.F v 1 := by
  refine af_ext _ fun w => ?_
  rw [map_sum]
  by_cases hw : w ∈ S
  · rw [Finset.sum_eq_single w (fun v _ hv => evalV_singleV_ne _ v _ hv.symm) (fun h => absurd hw h),
      evalV_singleV_same]
    have h1 := congrArg (evalV D.host.F w) he
    rw [map_mul] at h1
    exact mul_left_cancel₀ ((hS w).1 hw) (h1.trans (mul_one _).symm)
  · rw [Finset.sum_eq_zero fun v hv => evalV_singleV_ne _ v _ (fun h : w = v => hw (h ▸ hv))]
    by_contra h
    exact hw ((hS w).2 h)

theorem splitOffBad_of_suppSplit (V : HSp D) (N : ℕ) (h : GA D V) (hh : h ∈ GfC V)
    (hs : GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N (finHom V h).1) : FWT.SplitOffBad V N h := by
  classical
  obtain ⟨e₀, h1, h2, h3, h4⟩ := hs
  have hex : ∀ v : h2.toFinset, ∃ (e : AE D) (PP : HeightOneSpectrum (𝓞 D.host.E)), SplitAt D v.1 e ∧
      Formalism.L2.NTheta.IsIdemAt e PP ∧
      PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.1.asIdeal := by
    intro v
    obtain ⟨e, he⟩ := _root_.GlobalTheory.MovedSplit.exists_splitAt D v.1 (h3 v.1 (h2.mem_toFinset.1 v.2)).1
    obtain ⟨PP, hP⟩ := _root_.GlobalTheory.IdemPrime.exists_isIdemAt D v.1 e he
    exact ⟨e, PP, he, hP⟩
  choose ev Pv hsp hid hco using hex
  have hinj : Function.Injective Pv := fun v w hvw =>
    Subtype.ext (HeightOneSpectrum.ext (by rw [← hco, ← hco, hvw]))
  have hsum : ∑ v, ev v + cA D (∑ v, ev v) = fj D e₀ := by
    refine Eq.trans ?_ (congrArg (fj D) (idem_eq_sum e₀ h1 h2.toFinset (fun v => h2.mem_toFinset))).symm
    rw [map_sum, map_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_coe_sort h2.toFinset]
    exact Finset.sum_congr rfl fun v _ => (hsp v).2.2
  refine ⟨hh, ∑ v, ev v, Finset.univ.image Pv, ⟨⟨Function.extend Pv ev 0, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · intro PP hPP
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hPP
    rw [hinj.extend_apply]
    exact hid v
  · rw [Finset.sum_image fun v _ w _ hvw => hinj hvw]
    exact Finset.sum_congr rfl fun v _ => (hinj.extend_apply _ _ v).symm
  · rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun v _ => Finset.sum_eq_zero fun w _ => ?_
    by_cases hvw : v = w
    · subst hvw; exact (hsp v).2.1
    · exact (hsp v).orth (hsp w).conj fun e => hvw (Subtype.ext e)
  · intro PP hPP hm
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hPP
    refine (h3 v.1 (h2.mem_toFinset.1 v.2)).2 ?_
    rw [← hco, Ideal.mem_comap, map_natCast]
    exact hm
  · intro i j
    rw [hsum]
    refine GlobalTheory.UnitarySplit.parts_inj D _ _ ?_ ?_
    · have h5 : infPart D ((Formalism.L2.Theta.mt V h - 1) i j) = 0 := by
        have h6 : (Formalism.L2.Theta.mt V h).map (infPart D) = 1 := congrArg Units.val (show infHom V h = 1 from hh)
        have h7 := congrFun (congrFun h6 i) j
        rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero]
        refine h7.trans ?_
        by_cases e : i = j
        · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
        · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]
      rw [RingHom.map_mul, h5, mul_zero]
    · have h5 : finPart D ((Formalism.L2.Theta.mt V h - 1) i j) = ((finHom V h).1 - 1) i j := by
        rw [Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub]
        congr 1
        by_cases e : i = j
        · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
        · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]
      rw [RingHom.map_mul, h5]
      exact congrFun (congrFun h4 i) j

end Support

section Lattices

open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.AdLat GlobalTheory.UnRep.FullReps

variable {D : D7}

theorem hLat_eq (V : HSp D) (g : Bridge.Gf V) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : (Λ : Set (Fin V.rank → D.host.E)) = GlobalTheory.AdLat.latOf D.host.F g.1.1 (GlobalTheory.Member.latC V)) : Bridge.hLat V g = Λ := by
  unfold Bridge.hLat
  rw [← Submodule.span_eq Λ, hΛ, ← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq]
  congr 1
  ext x
  constructor
  · intro hx
    refine ⟨_, hx, ?_⟩
    rw [Matrix.mulVec_mulVec, Subgroup.coe_inv, Units.mul_inv, Matrix.one_mulVec]
    rfl
  · rintro ⟨z, hz, e⟩
    change (g.1⁻¹).1 *ᵥ fv D.host.F x ∈ hat D.host.F _
    rw [← e, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact hz

theorem hLat_one (V : HSp D) : Bridge.hLat V 1 = GlobalTheory.Member.latC V := by
  obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  refine hLat_eq V 1 _ ?_
  ext x
  rw [SetLike.mem_coe, ← (hat_rational_points_and_approx D.host.F D.host.E _ _ hfg hsp).1]
  simp [GlobalTheory.AdLat.latOf]

theorem exists_conjLat (V : HSp D) (hg : V.gram = 1) (hL : Bridge.hLat V 1 = stdLat D.host.E V.rank)
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H) (bad : ℕ) (h2 : 2 ∣ bad) (h : GA D V)
    (hs : GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) (bad * l.M) (finHom V h).1) :
    ∃ N : ℕ, (conjLat H (Bridge.hLat V (FWT.fin V h))).Unimod ∧ (conjLat H (Bridge.hLat V (FWT.fin V h))).TrivAt bad ∧
      (conjLat H (Bridge.hLat V (FWT.fin V h))).TrivAt l.M ∧ (conjLat H (Bridge.hLat V (FWT.fin V h))).LevOK N l.M ∧
      GenLat.SplitSupp H (conjLat H (Bridge.hLat V (FWT.fin V h))) := by
  have hc : GlobalTheory.Member.cF D = IsCMField.complexConj D.host.E := AlgEquiv.ext fun _ => rfl
  have hu := GlobalTheory.UnRep.Space.isUnA_finHom V h
  rw [show (HSpace.gram V)ᵀ = 1 by rw [hg, Matrix.transpose_one], hc] at hu
  rw [hc] at hs
  obtain ⟨Λ, N, h1, h3⟩ := exists_lat H l bad h2 (finHom V h) hu hs
  rw [hLat_one] at hL
  rw [hLat_eq V (FWT.fin V h) Λ (by rw [hL]; exact h1)]
  exact ⟨N, h3⟩

theorem exists_split_rep (V : HSp D) {J' : Subgroup (Bridge.Gf V)} {N₀ : ℕ} (hN₀ : 0 < N₀)
    (hK : ∀ k ∈ GfC V, GlobalTheory.Member.FinCong V N₀ k → FWT.fin V k ∈ J') {N : ℕ} (hN : 0 < N) (g : Bridge.Gf V) :
    ∃ h : GA D V, (h ∈ GfC V ∧ GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N (finHom V h).1) ∧
      ∃ (γ : GQ V) (k : J'), g = Bridge.ratF V γ * FWT.fin V h * k := by
  obtain ⟨_, g, rfl⟩ := g
  obtain ⟨γ, hγ, a, ha, h, hh, k, hk, e, hc, hs⟩ :=
    GlobalTheory.UnRep.Space.exists_rep_suppSplit D V (N * N₀) (Nat.mul_pos hN hN₀) g
  refine ⟨h, ⟨hh, suppSplit_mono (dvd_mul_right _ _) hs⟩, ⟨γ, hγ⟩,
    ⟨FWT.fin V k, hK k hk (finCong_mono (dvd_mul_left _ _) hc)⟩, Subtype.ext ?_⟩
  change finHom V g = finHom V γ * finHom V h * finHom V k
  rw [e, map_mul, map_mul, map_mul, show finHom V a = 1 from ha, mul_one]

end Lattices

section Row

open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.IndefR.FWT Formalism.L2.DIV

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

theorem exists_split_system (t : T0) {J' : Subgroup (Bridge.Gf (Vc D i))} (hle : J' ≤ levJ R i t)
    (hidx : J'.relIndex (levJ R i t) ≠ 0) {N₀ : ℕ} (hN₀ : 0 < N₀)
    (hK : ∀ k ∈ GfC (Vc D i), GlobalTheory.Member.FinCong (Vc D i) N₀ k → fin _ k ∈ J') {N : ℕ} (hN : 0 < N) :
    ∃ (m : ℕ) (h : Fin m → GA D (Vc D i)),
      (∀ k, h k ∈ GfC (Vc D i) ∧ GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N (finHom (Vc D i) (h k)).1) ∧
      Bridge.IsReps (Bridge.ratF (Vc D i)) J' (fun k => fin _ (h k)) ∧
      ∀ k, Finite (Bridge.stab (Bridge.ratF (Vc D i)) J' (fin _ (h k))) := by
  have hy : Bridge.IsReps (Bridge.ratF (Vc D i)) (levJ R i t) (R.B.L i t).pres.y := (R.B.L i t).pres.reps
  have hf : ∀ c, Finite (Bridge.stab (Bridge.ratF (Vc D i)) (levJ R i t) ((R.B.L i t).pres.y c)) := fun c =>
    Finite.of_equiv _ ((R.B.L i t).pres.stabI c).toEquiv
  obtain ⟨m, h, h1, h2⟩ := exists_reps_of_finiteIndex (Bridge.ratF (Vc D i)) hidx hy (fin (Vc D i))
    (fun h => h ∈ GfC (Vc D i) ∧ GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N (finHom (Vc D i) h).1)
    (exists_split_rep (Vc D i) hN₀ hK hN)
  exact ⟨m, h, h1, h2, fun k => finite_stab_of_reps _ hle hy hf _⟩

theorem exists_bad (t : T0) {b : ℕ} (hb : 0 < b) : ∃ bad : ℕ, 0 < bad ∧ b ∣ bad ∧
    ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  classical
  refine ⟨b * ∏ PP ∈ R.Pg ∪ R.Q t, Ideal.absNorm PP.asIdeal, Nat.mul_pos hb (Finset.prod_pos fun PP _ =>
    Nat.pos_of_ne_zero fun h => PP.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)), dvd_mul_right _ _, fun PP hPP => ?_⟩
  obtain ⟨u, hu⟩ := Finset.dvd_prod_of_mem (fun PP : Pl D.host.E => Ideal.absNorm PP.asIdeal) (Finset.mem_union.2 hPP)
  rw [hu, Nat.cast_mul, Nat.cast_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _))

theorem fin_mem_levJ (hβ : IsSDFrame (Vc D i) (R.βV i) (R.ΛV i) 1) (t : T0) {N : ℕ}
    (hN : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (k : GA D (Vc D i))
    (hk : GlobalTheory.Member.FinCong (Vc D i) N k) : fin _ k ∈ levJ R i t :=
  _root_.GlobalTheory.PrincInLevel.finCong_mem_levEnv D (Vc D i) (R.βV i) (R.ΛV i) (R.datVt i t) N k hβ hN hk

theorem exists_repsR_at (K' : Type) [Field K'] (t : T0) {J' : Subgroup (Bridge.Gf (Vc D i))} (hle : J' ≤ levJ R i t)
    (hidx : J'.relIndex (levJ R i t) ≠ 0) {N₀ : ℕ} (hN₀ : 0 < N₀)
    (hK : ∀ k ∈ GfC (Vc D i), GlobalTheory.Member.FinCong (Vc D i) N₀ k → fin _ k ∈ J') {bad : ℕ} (hb : 0 < bad)
    (hbad : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) {M : ℕ} (hM : 0 < M) :
    ∃ (m : ℕ) (h : Fin m → GA D (Vc D i)) (gam : Fin m → ℕ) (vol : K'),
      RepsR R i t h bad J' (fun k => Bridge.hLat (Vc D i) (fin _ (h k))) gam vol ∧ (∀ k, 0 < gam k) ∧
      ∀ k, GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) (bad * M) (finHom (Vc D i) (h k)).1 := by
  obtain ⟨m, h, h1, h2, h3⟩ := exists_split_system R i t hle hidx hN₀ hK (Nat.mul_pos hb hM)
  refine ⟨m, h, _, _, ⟨hb.ne', hbad, hle, hidx, rfl, h2, fun k => ⟨?_, rfl, rfl⟩⟩, fun k => ?_, fun k => (h1 k).2⟩
  · exact splitOffBad_of_suppSplit _ _ _ (h1 k).1 (suppSplit_mono (dvd_mul_right _ _) (h1 k).2)
  · have := h3 k
    exact Nat.card_pos

theorem exists_repsR (hβ : IsSDFrame (Vc D i) (R.βV i) (R.ΛV i) 1) (K' : Type) [Field K'] (t : T0) {b : ℕ} (hb : 0 < b) :
    ∃ (Cl : Type) (_ : Fintype Cl) (h : Cl → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))) (bad : ℕ)
      (Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)) (gam : Cl → ℕ) (vol : K'),
      RepsR R i t h bad J' Lh gam vol ∧ b ∣ bad ∧ (∀ k, 0 < gam k) ∧ vol ≠ 0 := by
  obtain ⟨bad, h0, h1, h2⟩ := exists_bad R t hb
  obtain ⟨m, h, gam, vol, hr, hg, -⟩ := exists_repsR_at R i K' t le_rfl (by simp) h0
    (fun k _ hk => fin_mem_levJ R i hβ t h2 k hk) h0 h2 one_pos
  exact ⟨Fin m, inferInstance, h, _, bad, _, gam, vol, hr, h1, hg, by rw [hr.2.2.2.2.1]; simp⟩

theorem exists_repsR_repsOK (hβ : IsSDFrame (Vc D i) (R.βV i) (R.ΛV i) 1) (hV : VStd D i) (K' : Type) [Field K'] (t : T0)
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (l : Level H) {b : ℕ} (hb : 0 < b) :
    ∃ (Cl : Type) (_ : Fintype Cl) (h : Cl → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))) (bad : ℕ)
      (Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)) (gam : Cl → ℕ) (vol : K')
      (La : Cl → GenLat D.host.E (Vc D i).rank) (Nc : Cl → ℕ),
      RepsR R i t h bad J' Lh gam vol ∧ b ∣ bad ∧ vol ≠ 0 ∧ RepsOK (l := l) bad La Nc gam ∧ LatPin Lh La := by
  obtain ⟨bad, h0, h1, h2⟩ := exists_bad R t (Nat.mul_pos two_pos hb)
  obtain ⟨m, h, gam, vol, hr, hg, hs⟩ := exists_repsR_at R i K' t le_rfl (by simp) h0
    (fun k _ hk => fin_mem_levJ R i hβ t h2 k hk) h0 h2 (M := l.M) (by have := l.three_le; omega)
  choose Nc c1 c2 c3 c4 c5 using fun k =>
    exists_conjLat (Vc D i) hV.1 hV.2 H l bad (dvd_of_mul_right_dvd h1) (h k) (hs k)
  exact ⟨Fin m, inferInstance, h, _, bad, _, gam, vol, _, Nc, hr, dvd_of_mul_left_dvd h1,
    by rw [hr.2.2.2.2.1]; simp, fun k => ⟨c1 k, c2 k, c3 k, c4 k, hg k, c5 k⟩, fun _ _ => Iff.rfl⟩

theorem exists_repsR_repsCov (hβ : IsSDFrame (Vc D i) (R.βV i) (R.ΛV i) 1) (hV : VStd D i) (K' : Type) [Field K']
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)
    {Tp : Type} (tup : Tp → T0) (dδ : Tp → DeltaDat Xo c (Vc D i).rank) :
    ∃ (Cl : Tp → Type) (_ : ∀ t, Fintype (Cl t)) (h : ∀ t, Cl t → GA D (Vc D i))
      (J' : Tp → Subgroup (Bridge.Gf (Vc D i))) (bad : Tp → ℕ)
      (Lh : ∀ t, Cl t → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)) (gam : ∀ t, Cl t → ℕ) (vol : Tp → K')
      (La : ∀ t, Cl t → GenLat D.host.E (Vc D i).rank) (Nc : ∀ t, Cl t → ℕ),
      (∀ t, RepsR R i (tup t) (h t) (bad t) (J' t) (Lh t) (gam t) (vol t) ∧ vol t ≠ 0) ∧
      (∀ t, 0 < bad t ∧ BadPin (bad t) (D.host.QS * D.host.q) D.host.d (D.host.g 0 * D.host.g 1)) ∧
      RepsCov Xo c Cl dδ bad Lh La Nc gam := by
  have hb : 0 < 2 * (D.host.QS * D.host.q * (D.host.d * (D.host.g 0 * D.host.g 1))) :=
    Nat.mul_pos two_pos (Nat.mul_pos (Nat.mul_pos D.host.QS_pos D.host.hyp.1.pos) (Nat.mul_pos D.host.hyp.2.1.pos
      (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos)))
  choose Cl fCl h J' bad Lh gam vol La Nc h1 h2 h3 h4 h5 using fun t =>
    exists_repsR_repsOK R i hβ hV K' (tup t) (dδ t).l₂ hb
  refine ⟨Cl, fCl, h, J', bad, Lh, gam, vol, La, Nc, fun t => ⟨h1 t, h3 t⟩,
    fun t => ⟨Nat.pos_of_ne_zero (h1 t).1, dvd_of_mul_right_dvd (h2 t), ?_, ?_, ?_⟩, fun t => ⟨h4 t, h5 t⟩⟩
  · exact dvd_of_mul_right_dvd (dvd_of_mul_left_dvd (h2 t))
  · exact dvd_of_mul_right_dvd (dvd_of_mul_left_dvd (dvd_of_mul_left_dvd (h2 t)))
  · exact dvd_of_mul_left_dvd (dvd_of_mul_left_dvd (dvd_of_mul_left_dvd (h2 t)))

theorem reps_exist (F : Face D A) (hC : R.Char F) (K' : Type) [Field K'] :
    (∀ (t : T0) (b : ℕ), 0 < b →
      ∃ (Cl : Type) (_ : Fintype Cl) (h : Cl → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))) (bad : ℕ)
        (Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)) (gam : Cl → ℕ) (vol : K'),
        RepsR R i t h bad J' Lh gam vol ∧ b ∣ bad ∧ (∀ k, 0 < gam k) ∧ vol ≠ 0) ∧
    (VStd D i → ∀ {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)
      {Tp : Type} (tup : Tp → T0) (dδ : Tp → DeltaDat Xo c (Vc D i).rank),
      ∃ (Cl : Tp → Type) (_ : ∀ t, Fintype (Cl t)) (h : ∀ t, Cl t → GA D (Vc D i))
        (J' : Tp → Subgroup (Bridge.Gf (Vc D i))) (bad : Tp → ℕ)
        (Lh : ∀ t, Cl t → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)) (gam : ∀ t, Cl t → ℕ) (vol : Tp → K')
        (La : ∀ t, Cl t → GenLat D.host.E (Vc D i).rank) (Nc : ∀ t, Cl t → ℕ),
        (∀ t, RepsR R i (tup t) (h t) (bad t) (J' t) (Lh t) (gam t) (vol t) ∧ vol t ≠ 0) ∧
        (∀ t, 0 < bad t ∧ BadPin (bad t) (D.host.QS * D.host.q) D.host.d (D.host.g 0 * D.host.g 1)) ∧
        RepsCov Xo c Cl dδ bad Lh La Nc gam) :=
  ⟨fun t _ hb => exists_repsR R i (hC.lev.βV i) K' t hb,
    fun hV _ _ _ Xo c _ tup dδ => exists_repsR_repsCov R i (hC.lev.βV i) hV K' Xo c tup dδ⟩

end Row

end GlobalTheory.SplitReps
