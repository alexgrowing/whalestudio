import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.GradedClassDecomposition
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.DetectPt
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.HfracOf

noncomputable section

namespace Formalism.MainNotions.N.Ln03.K8

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct

theorem X_pow_dvd_of_components {ι R : Type} [CommRing R] (F : PowerSeries (ι → R)) (e : ℕ)
    (h : ∀ i, PowerSeries.X ^ e ∣ PowerSeries.map (Pi.evalRingHom (fun _ => R) i) F) :
    PowerSeries.X ^ e ∣ F := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  funext i
  have := (PowerSeries.X_pow_dvd_iff.1 (h i)) m hm
  rw [PowerSeries.coeff_map] at this
  simpa using this

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n}

theorem detect [IsFractionRing O LL] (hP4 : LevelMapHodgeFiltration W) (hSat : Sat W) (hcrys : IsCrys PD T.ρ)
    (hLb : ∀ (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hfree : (latOf C).Free c)
    (ϖ : O) (ell : ℕ)
    (hcompl : ∀ s < ell, ∀ (k : ℕ) (a : PowerSeries O), PowerSeries.X ^ k ∣ rhoL hR c s a →
      ∃ (N : ℕ) (z : PowerSeries O), PowerSeries.C (ϖ ^ N) * a = (baseIdOf hR).Bs.p s ^ k * z)
    (hϖ : ∃ (N : ℕ) (u : O), ((PD.p : ℕ) : O) ^ N = ϖ * u)
    (s : ℕ) (hs : s < ell) (hfilt : IsFilt (FilD W T c s)) (e : ℕ) (y : C.V) (hy : y ∈ (latOf C).N c)
    (h : ∀ (ζ : Rs LL PD.p s) (k : ℤ),
      (⟨Lb.levB T c ζ ⟨C.t c y, hy⟩ k, Lb.mem T c ζ ⟨C.t c y, hy⟩ k⟩ : Dc W T c) ∈
        FilD W T c s ((e : ℤ) - k)) :
    ∃ y' ∈ (latOf C).N c, y = (baseIdOf hR).Bs.p s ^ e • y' := by
  classical
  obtain ⟨r, b, hind, hspan⟩ := hfree
  have hb : ∀ j, b j ∈ (latOf C).N c := fun j => hspan ▸ Submodule.subset_span ⟨j, rfl⟩
  obtain ⟨hfd, hr⟩ := rank_eq hP3 hmod b hind hspan
  have hy' : y ∈ Submodule.span (PowerSeries O) (Set.range b) := hspan.symm ▸ hy
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hy'
  have hyN : (⟨C.t c y, hy⟩ : ↥(W.N T)) =
      ∑ j, (baseIdOf hR).d (a j) • (⟨C.t c (b j), hb j⟩ : ↥(W.N T)) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    rw [← ha, coord_t_finset_sum]
    exact Finset.sum_congr rfl fun j _ => C.t_smul c (a j) (b j)

  have hdiv : ∀ (ζ : Rs LL PD.p s) (j : Fin r), PowerSeries.X ^ e ∣ W.lev c ζ ((baseIdOf hR).d (a j)) := by
    intro ζ
    have := hfd
    refine detect_pt (FilD W T c s) hfilt hr
      (fun j k => (⟨Lb.levB T c ζ ⟨C.t c (b j), hb j⟩ k, Lb.mem T c ζ _ k⟩ : Dc W T c))
      (fun j => ?_) (fun j k => levB_mem_fil hP4 hcrys hLb s ζ _ k)
      (span_classes hP4 hcrys hLb hmod s hfilt ζ b hb hspan)
      (fun j => W.lev c ζ ((baseIdOf hR).d (a j))) e ?_
    · obtain ⟨m, hm⟩ := Lb.supp T c ζ ⟨C.t c (b j), hb j⟩
      exact ⟨m, fun k hk => Subtype.ext (hm k hk)⟩
    · intro k
      have hk := h ζ k
      change ιV PD (LL := LL) (V := T.V) (Lb.levB T c ζ ⟨C.t c y, hy⟩ k) ∈
        FilLev W T c s ((e : ℤ) - k) at hk
      rw [← hLb, hyN, map_sum, Finset.sum_apply] at hk
      show ((ιV PD (LL := LL) (V := T.V)).comp (DcrisL PD T.ρ (W.emb c)).subtype)
        (∑ j, ∑ᶠ i : ℕ, PowerSeries.coeff i (W.lev c ζ ((baseIdOf hR).d (a j))) •
          (⟨Lb.levB T c ζ ⟨C.t c (b j), hb j⟩ (k - i), Lb.mem T c ζ _ (k - i)⟩ : Dc W T c)) ∈
        FilLev W T c s ((e : ℤ) - k)
      suffices heq : ∀ j, ((ιV PD (LL := LL) (V := T.V)).comp (DcrisL PD T.ρ (W.emb c)).subtype)
          (∑ᶠ i : ℕ, PowerSeries.coeff i (W.lev c ζ ((baseIdOf hR).d (a j))) •
            (⟨Lb.levB T c ζ ⟨C.t c (b j), hb j⟩ (k - i), Lb.mem T c ζ _ (k - i)⟩ : Dc W T c)) =
          W.levN T c ζ ((baseIdOf hR).d (a j) • (⟨C.t c (b j), hb j⟩ : ↥(W.N T))) k by
        rw [map_sum, Finset.sum_congr rfl fun j _ => heq j]
        exact hk
      intro j
      rw [W.levN_smul]
      obtain ⟨m, hm⟩ := Lb.supp T c ζ ⟨C.t c (b j), hb j⟩
      have hfin : (Function.support fun i : ℕ => PowerSeries.coeff i (W.lev c ζ ((baseIdOf hR).d (a j))) •
          (⟨Lb.levB T c ζ ⟨C.t c (b j), hb j⟩ (k - i), Lb.mem T c ζ _ (k - i)⟩ : Dc W T c)).Finite := by
        refine (Finset.range ((k - m).toNat + 1)).finite_toSet.subset fun i hi => ?_
        rw [Finset.coe_range, Set.mem_Iio]
        by_contra hlt
        apply hi
        have h0 : (⟨Lb.levB T c ζ ⟨C.t c (b j), hb j⟩ (k - i), Lb.mem T c ζ _ (k - i)⟩ : Dc W T c) = 0 :=
          Subtype.ext (hm _ (by omega))
        show _ • _ = 0
        rw [h0, smul_zero]
      rw [map_finsum _ hfin]
      refine finsum_congr fun i => ?_
      rw [map_smul, LinearMap.comp_apply, Submodule.subtype_apply, ← hLb]

  have hcj : ∀ j, ∃ (N : ℕ) (z : PowerSeries O),
      PowerSeries.C (ϖ ^ N) * a j = (baseIdOf hR).Bs.p s ^ e * z := by
    intro j
    refine hcompl s hs e (a j) (X_pow_dvd_of_components _ e fun ζ => ?_)
    rw [map_eval_rhoL]
    exact hdiv ζ j
  choose Nj z hz using hcj
  obtain ⟨N', u, hu⟩ := hϖ
  set Nt := ∑ j, Nj j with hNt
  set K := N' * Nt with hK
  have hlK : ∀ j, PowerSeries.C (((PD.p : ℕ) : O) ^ K) * a j =
      (baseIdOf hR).Bs.p s ^ e * (PowerSeries.C (u ^ Nt * ϖ ^ (Nt - Nj j)) * z j) := by
    intro j
    have hle : Nj j ≤ Nt := Finset.single_le_sum (fun j _ => Nat.zero_le (Nj j)) (Finset.mem_univ j)
    have e1 : ((PD.p : ℕ) : O) ^ K = u ^ Nt * ϖ ^ (Nt - Nj j) * ϖ ^ Nj j := by
      rw [hK, pow_mul, hu, mul_pow, mul_assoc, ← pow_add, Nat.sub_add_cancel hle, mul_comm]
    rw [e1, map_mul, mul_assoc, hz j]
    ring
  set w : C.V := ∑ j, (PowerSeries.C (u ^ Nt * ϖ ^ (Nt - Nj j)) * z j) • b j with hw
  have hwN : w ∈ (latOf C).N c :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hb j)
  have hyw : PowerSeries.C (((PD.p : ℕ) : O) ^ K) • y = (baseIdOf hR).Bs.p s ^ e • w := by
    rw [← ha, Finset.smul_sum, hw, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, smul_smul, hlK j]

  have hd : (baseIdOf hR).d ((baseIdOf hR).Bs.p s ^ e) =
      ∏ s' ∈ Finset.range (s + 1), pS W s' ^ (if s' = s then e else 0) := by
    rw [map_pow, BaseId.d_p, Finset.prod_eq_single s (fun s' _ hs' => by rw [if_neg hs', pow_zero])
      (fun hns => absurd (Finset.mem_range.2 (Nat.lt_succ_self s)) hns), if_pos rfl]
  have hdl : (baseIdOf hR).d (PowerSeries.C (((PD.p : ℕ) : O) ^ K)) = ((PD.p : ℕ) : LetA O n) ^ K := by
    rw [BaseId.d_C, map_pow, map_natCast]
  have hNΔ : ∀ x : W.DD T, x ∈ W.N T → (∀ δ ∈ W.DelF, W.γD T δ x = x) → x ∈ W.NΔ T :=
    fun x h1 h2 => ⟨h1, h2⟩
  have hx : C.t c y ∈ mulSet W T ((baseIdOf hR).d ((baseIdOf hR).Bs.p s ^ e)) (W.NΔ T) := by
    refine hSat T ((baseIdOf hR).d ((baseIdOf hR).Bs.p s ^ e)) 1 hcrys
      ⟨0, (baseIdOf hR).d ((baseIdOf hR).Bs.p s ^ e), ⟨fun s' => if s' = s then e else 0, s + 1, hd⟩, by simp⟩
      ⟨0, 1, ⟨fun _ => 0, 0, by simp⟩, by simp⟩ (C.t c y) (fun δ hδ => C.t_Δ c y δ hδ) ?_ ?_
    · rw [one_smul]
      exact hNΔ _ hy (fun δ hδ => C.t_Δ c y δ hδ)
    · refine ⟨K, C.t c w, hNΔ _ hwN (fun δ hδ => C.t_Δ c w δ hδ), ?_⟩
      rw [← hdl, ← Coord.t_smul, hyw, Coord.t_smul]
  obtain ⟨z', hz', hxz⟩ := hx
  have hlet : (letE c : LetA O n) • ((letE c : LetA O n) • z') = (letE c : LetA O n) • z' := by
    rw [smul_smul, letE_mul_self]
  have hΔ : ∀ δ ∈ W.DelF, W.γD T δ ((letE c : LetA O n) • z') = (letE c : LetA O n) • z' := by
    intro δ hδ
    rw [γD_smulA, γA_letE, hz'.2 δ hδ]
  obtain ⟨y'', hy''⟩ := C.t_surj c _ hlet hΔ
  refine ⟨y'', ?_, ?_⟩
  · show C.t c y'' ∈ W.N T
    rw [hy'']
    exact (W.N T).smul_mem _ hz'.1
  · apply C.t_inj c
    rw [Coord.t_smul, hy'', smul_smul, mul_comm, ← smul_smul, ← hxz, C.t_letter]

end Formalism.MainNotions.N.Ln03.K8

end
