import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

noncomputable section

namespace GlobalTheory.EtaleExact

theorem eq_top_of_span_image {E R D M : Type} [CommRing E] [CommRing R] [AddCommGroup D]
    [Module E D] [AddCommGroup M] [Module R M] [Module.Free E D] [Module.Finite E D]
    (io : E →+* R) (j : D →+ M) (hj : ∀ e x, j (e • x) = io e • j x)
    (hm : ∀ m : Ideal E, m.IsMaximal → m.map io ≠ ⊤)
    (hrank : Nontrivial R → Module.finrank E D = Module.finrank R M)
    (hspan : Submodule.span R (Set.range j) = ⊤)
    (N : Submodule E D) (hN : Submodule.span R (j '' (N : Set D)) = ⊤) : N = ⊤ := by
  classical
  by_contra hne
  obtain ⟨N', hN', hle⟩ := (eq_top_or_exists_le_coatom N).resolve_left hne
  obtain ⟨m, hmax, ⟨ψ⟩⟩ := isSimpleModule_iff_quot_maximal.1 (isSimpleModule_iff_isCoatom.2 hN')
  have hm' := hm m hmax
  haveI : Nontrivial E := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hmax.ne_top (Subsingleton.elim _ _)
  haveI : Nontrivial R := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hm' (Subsingleton.elim _ _)
  let b := Module.Free.chooseBasis E D
  have hsp : ⊤ ≤ Submodule.span R (Set.range fun i => j (b i)) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [← b.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hj]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let c := basisOfTopLeSpanOfCardEqFinrank (fun i => j (b i)) hsp
    (by rw [← hrank inferInstance, Module.finrank_eq_card_chooseBasisIndex])
  have hc : ∀ i, c i = j (b i) := fun i => by simp [c]
  let f : D →ₗ[E] E ⧸ m := ψ.toLinearMap ∘ₗ N'.mkQ
  let q : E ⧸ m →+* R ⧸ m.map io := Ideal.quotientMap _ io Ideal.le_comap_map
  let F : M →ₗ[R] R ⧸ m.map io := c.constr R fun i => q (f (b i))
  have hF : ∀ x, F (j x) = q (f x) := by
    intro x
    rw [← b.sum_repr x]
    simp only [map_sum, hj, map_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hc, Module.Basis.constr_basis, Algebra.smul_def, Algebra.smul_def, map_mul]
    rfl
  have hF0 : F = 0 := by
    rw [← LinearMap.ker_eq_top, eq_top_iff, ← hN, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have : N'.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero _).2 (hle hx)
    change F (j x) = 0
    rw [hF]
    simp [f, this]
  obtain ⟨x, hx⟩ : ∃ x, f x = 1 := (ψ.surjective.comp N'.mkQ_surjective) 1
  have h1 := hF x
  rw [hF0, hx, map_one] at h1
  exact hm' (Ideal.Quotient.zero_eq_one_iff.1 h1)

theorem mem_map_C {O : Type} [CommRing O] (J : Ideal O) (hJ : J.FG) (f : PowerSeries O)
    (hf : ∀ k, PowerSeries.coeff k f ∈ J) : f ∈ J.map (PowerSeries.C : O →+* PowerSeries O) := by
  obtain ⟨d, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hJ
  have h : ∀ k, ∃ c : Fin d → O, ∑ i, c i • g i = PowerSeries.coeff k f := fun k =>
    (Submodule.mem_span_range_iff_exists_fun O).1 (hg ▸ hf k)
  choose c hc using h
  have : f = ∑ i, PowerSeries.mk (fun k => c k i) * PowerSeries.C (g i) := by
    ext k
    simp [← hc k]
  rw [this]
  refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ?_)
  rw [← hg]
  exact Submodule.subset_span ⟨i, rfl⟩

theorem mem_radical_of_mem {O E : Type} [CommRing O] [IsNoetherianRing O] [CommRing E] (p : ℕ)
    (hO : ∀ c : O, IsUnit c ∨ ∃ k : ℕ, (p : O) ∣ c ^ k)
    (ψ : PowerSeries O →+* E) (hX : IsUnit (ψ PowerSeries.X)) (m : Ideal E) (hm : m ≠ ⊤)
    (hp : (Ideal.span {(p : E)}).radical ≤ m) (f : PowerSeries O) (hf : ψ f ∈ m) :
    ψ f ∈ (Ideal.span {(p : E)}).radical := by
  classical
  let J : Ideal O := (Ideal.span {(p : O)}).radical
  have key : ∀ g : PowerSeries O, (∀ k, PowerSeries.coeff k g ∈ J) →
      ψ g ∈ (Ideal.span {(p : E)}).radical := by
    intro g hg
    have h1 := mem_map_C J (IsNoetherian.noetherian J) g hg
    have h2 : J.map (PowerSeries.C : O →+* PowerSeries O) ≤
        ((Ideal.span {(p : E)}).radical).comap ψ := by
      rw [Ideal.map_le_iff_le_comap]
      rintro c ⟨k, hk⟩
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 hk
      refine ⟨k, Ideal.mem_span_singleton.2 ⟨ψ (PowerSeries.C d), ?_⟩⟩
      rw [← map_pow, ← map_pow, hd, map_mul, map_mul, map_natCast, map_natCast]
    exact h2 h1
  by_cases h : ∀ k, PowerSeries.coeff k f ∈ J
  · exact key f h
  exfalso
  push_neg at h
  let k := Nat.find h
  have hk : IsUnit (PowerSeries.coeff k f) := (hO _).resolve_right fun ⟨r, hr⟩ =>
    Nat.find_spec h ⟨r, Ideal.mem_span_singleton.2 hr⟩
  have ht : ψ (PowerSeries.trunc k f : Polynomial O) ∈ m := by
    refine hp (key _ fun i => ?_)
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs with hi
    · exact not_not.1 (Nat.find_min h hi)
    · exact J.zero_mem
  have hu : IsUnit (PowerSeries.mk fun i => PowerSeries.coeff (i + k) f) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simpa using hk
  have he := PowerSeries.eq_shift_mul_X_pow_add_trunc k f
  rw [he, map_add] at hf
  have h3 := m.sub_mem hf ht
  rw [add_sub_cancel_right, map_mul, map_pow] at h3
  exact hm (Ideal.eq_top_of_isUnit_mem _ h3 ((hu.map ψ).mul (hX.pow k)))

theorem map_maximal_ne_top {O E R : Type} [CommRing O] [IsNoetherianRing O] [CommRing E]
    [CommRing R] (n : ℕ) [NeZero n] (p : ℕ) (hO : ∀ c : O, IsUnit c ∨ ∃ k : ℕ, (p : O) ∣ c ^ k)
    (a : LetA O n →+* E) (hπ : IsUnit (a letπ)) [IsAdicComplete (Ideal.span {(p : E)}) E]
    (hd : ∀ x : E, ∃ (f : LetA O n) (r : ℕ), x * a (letπ ^ r) - a f ∈ Ideal.span {(p : E)})
    (io : E →+* R) (hio : Function.Injective io)
    (hsep : ∀ x : R, (∀ k : ℕ, (p : R) ^ k ∣ x) → x = 0)
    (m : Ideal E) (hm : m.IsMaximal) : m.map io ≠ ⊤ := by
  classical
  intro htop
  have hpm : Ideal.span {(p : E)} ≤ m :=
    (IsAdicComplete.le_jacobson_bot (Ideal.span {(p : E)})).trans
      (sInf_le ⟨bot_le, hm⟩)
  have hrad : (Ideal.span {(p : E)}).radical ≤ m := hm.isPrime.radical_le_iff.2 hpm
  obtain ⟨i, hi⟩ : ∃ i, a (letE i) ∉ m := by
    by_contra h
    push_neg at h
    have h1 : ∑ i, (letE i : LetA O n) = 1 := by
      funext k
      simp [letE, Finset.sum_apply, Pi.single_apply]
    have := m.sum_mem (t := Finset.univ) fun i _ => h i
    rw [← map_sum, h1, map_one] at this
    exact hm.ne_top ((Ideal.eq_top_iff_one _).2 this)
  let ψ : PowerSeries O →+* E := a.comp (Pi.constRingHom (ZMod n) (PowerSeries O))
  have hψ : ∀ f : LetA O n, a (letE i) * a f = a (letE i) * ψ (f i) := by
    intro f
    change _ = a (letE i) * a (Function.const _ (f i))
    rw [← map_mul, ← map_mul]
    congr 1
    funext k
    by_cases hk : k = i
    · subst hk; simp [letE]
    · simp [letE, hk]
  have hidem : a (letE i) * a (letE i) = a (letE i) := by
    rw [hψ]; simp [letE]
  have hx : ∀ x ∈ m, a (letE i) * x ∈ (Ideal.span {(p : E)}).radical := by
    intro x hx
    obtain ⟨f, r, hf⟩ := hd x
    have h1 : a f ∈ m := by
      have := m.sub_mem (m.mul_mem_right (a (letπ ^ r)) hx) (hpm hf)
      rwa [sub_sub_cancel] at this
    have h2 : ψ (f i) ∈ m := by
      have := m.mul_mem_left (a (letE i)) h1
      rw [hψ] at this
      exact (hm.isPrime.mem_or_mem this).resolve_left hi
    have h3 := mem_radical_of_mem p hO ψ hπ m hm.ne_top hrad _ h2
    have h4 : a (letE i) * x * a (letπ ^ r) ∈ (Ideal.span {(p : E)}).radical := by
      have h5 := Ideal.add_mem _ (Ideal.mul_mem_left _ (a (letE i)) (Ideal.le_radical hf))
        (Ideal.mul_mem_left _ (a (letE i)) h3)
      rw [← hψ] at h5
      convert h5 using 1
      ring
    rw [map_pow] at h4
    exact (Ideal.mul_unit_mem_iff_mem _ (hπ.pow r)).1 h4
  let I : Ideal R := Submodule.comap (LinearMap.mulLeft R (io (a (letE i))))
    ((Ideal.span {(p : R)}).radical)
  have hI : m.map io ≤ I := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hxm
    obtain ⟨k, hk⟩ := hx x hxm
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 hk
    refine ⟨k, Ideal.mem_span_singleton.2 ⟨io d, ?_⟩⟩
    change (io (a (letE i)) * io x) ^ k = _
    rw [← map_mul, ← map_pow, hd, map_mul, map_natCast]
  have h1 : (1 : R) ∈ I := hI (htop ▸ Submodule.mem_top)
  obtain ⟨k, hk⟩ := h1
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 hk
  change (io (a (letE i)) * 1) ^ k = _ at hd
  rw [mul_one] at hd
  have hid : IsIdempotentElem (io (a (letE i))) := by
    rw [IsIdempotentElem, ← map_mul, hidem]
  have h2 : (p : R) ∣ io (a (letE i)) := by
    refine ⟨d * io (a (letE i)), ?_⟩
    rw [← mul_assoc, ← hd, ← pow_succ, hid.pow_succ_eq]
  have h3 : io (a (letE i)) = 0 := by
    refine hsep _ fun r => ?_
    have := pow_dvd_pow_of_dvd h2 (r + 1)
    rw [hid.pow_succ_eq] at this
    exact (pow_dvd_pow _ (Nat.le_succ r)).trans this
  apply hi
  rw [hio (h3.trans (map_zero io).symm)]
  exact m.zero_mem

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA)

def latMap {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) : ↥T.L.T →ₗ[O] ↥T'.L.T :=
  (f.f.restrictScalars O).restrict f.T_le

theorem jD_map' {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (x : W.DD T) :
    E.jD T' (W.map f x) = (latMap f).baseChange RW (E.jD T x) := E.jD_map f x

include E in
theorem finite_DD (T : LocLat G Qp LL O) : Module.Finite W.EE (W.DD T) := by
  haveI : Nontrivial O := (algebraMap O LL).domain_nontrivial
  haveI := T.L.free
  haveI : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg
  haveI := (W.DD_free T).1
  rcases Nat.eq_zero_or_pos (Module.finrank O ↥T.L.T) with h | h
  · haveI : Subsingleton ↥T.L.T := Module.finrank_eq_zero_iff_of_free O _ |>.1 h
    haveI : Subsingleton (W.DD T) := (E.jD_inj T).subsingleton
    infer_instance
  · rcases subsingleton_or_nontrivial W.EE with hE | hE
    · haveI := Module.subsingleton W.EE (W.DD T)
      infer_instance
    rw [← (W.DD_free T).2] at h
    exact Module.finite_of_finrank_pos h

theorem ioE_injective : Function.Injective E.ioE := by
  haveI : Nontrivial O := (algebraMap O LL).domain_nontrivial
  haveI := W.one.L.free
  haveI : Module.Finite O ↥W.one.L.T := Module.Finite.iff_fg.2 W.one.L.fg
  haveI := (W.DD_free W.one).1
  rcases subsingleton_or_nontrivial W.EE with h | h
  · exact Function.injective_of_subsingleton _
  obtain ⟨e, he, hT⟩ := W.one_line
  haveI : Nontrivial ↥W.one.L.T :=
    ⟨⟨⟨e, hT ▸ Submodule.mem_span_singleton_self e⟩, 0, fun h => he (congrArg Subtype.val h)⟩⟩
  haveI : Nontrivial (W.DD W.one) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have h1 := (W.DD_free W.one).2
    rw [Module.finrank_zero_of_subsingleton] at h1
    exact not_subsingleton _ ((Module.finrank_eq_zero_iff_of_free O _).1 h1.symm)
  let b := Module.Free.chooseBasis W.EE (W.DD W.one)
  obtain ⟨i⟩ := b.index_nonempty
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 : x • b i = 0 := by
    apply E.jD_inj
    rw [E.jD_smul, hx, zero_smul, map_zero]
  simpa using congrArg (fun y => b.repr y i) h1

theorem eq_top_DD (hm : ∀ m : Ideal W.EE, m.IsMaximal → m.map E.ioE.toRingHom ≠ ⊤)
    (T : LocLat G Qp LL O) (N : Submodule W.EE (W.DD T))
    (hN : Submodule.span RW (E.jD T '' (N : Set (W.DD T))) = ⊤) : N = ⊤ := by
  haveI : Nontrivial O := (algebraMap O LL).domain_nontrivial
  haveI := T.L.free
  haveI := (W.DD_free T).1
  haveI := finite_DD E T
  refine eq_top_of_span_image E.ioE.toRingHom (E.jD T).toAddMonoidHom (E.jD_smul T) hm
    (fun _ => ?_) (E.jD_span T) N hN
  rw [(W.DD_free T).2, Module.finrank_baseChange]

theorem span_range_map {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) :
    Submodule.span RW (E.jD T' '' (LinearMap.range (W.map f) : Set (W.DD T'))) =
      LinearMap.range ((latMap f).baseChange RW) := by
  rw [LinearMap.range_eq_map ((latMap f).baseChange RW), ← E.jD_span T, Submodule.map_span]
  congr 1
  ext y
  simp only [Set.mem_image, SetLike.mem_coe, LinearMap.mem_range, Set.mem_range,
    exists_exists_eq_and, jD_map']

theorem exact_of_tie (hm : ∀ m : Ideal W.EE, m.IsMaximal → m.map E.ioE.toRingHom ≠ ⊤)
    (T Yt Z : LocLat G Qp LL O) (ι : LatHom T.L Yt.L) (π : LatHom Yt.L Z.L)
    (h : IsSESLat (Qp := Qp) ι π) :
    Function.Injective (W.map ι) ∧ Function.Exact (W.map ι) (W.map π) ∧
      Function.Surjective (W.map π) := by
  obtain ⟨h1, -, h3, h4, h5⟩ := h
  have hι : Function.Injective (latMap ι) := fun x y hxy =>
    Subtype.ext (h1 (congrArg Subtype.val hxy))
  have hπ : Function.Surjective (latMap π) := fun y => by
    obtain ⟨x, hx, hxy⟩ := h3 y y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hex : Function.Exact (latMap ι) (latMap π) := fun x => by
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := (h4 x).1 (congrArg Subtype.val hx)
      exact ⟨⟨y, h5 y (hy ▸ x.2)⟩, Subtype.ext hy⟩
    · rintro ⟨y, rfl⟩
      exact Subtype.ext ((h4 _).2 ⟨y, rfl⟩)
  haveI := Z.L.free
  have hπR : Function.Surjective ((latMap π).baseChange RW) :=
    LinearMap.lTensor_surjective RW hπ
  have hexR : Function.Exact ((latMap ι).baseChange RW) ((latMap π).baseChange RW) :=
    lTensor_exact RW hex hπ
  have hιR : Function.Injective ((latMap ι).baseChange RW) := by
    obtain ⟨s, hs⟩ := (latMap π).exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hπ)
    obtain ⟨r, hr⟩ : ∃ r, r ∘ₗ latMap ι = LinearMap.id :=
      ((hex.split_tfae hι hπ).out 0 1).1 (show ∃ s, latMap π ∘ₗ s = LinearMap.id from ⟨s, hs⟩)
    refine Function.LeftInverse.injective (g := r.baseChange RW) fun x => ?_
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hr, LinearMap.baseChange_id]
    rfl
  have hsurj : Function.Surjective (W.map π) := by
    rw [← LinearMap.range_eq_top]
    refine eq_top_DD E hm Z _ ?_
    rw [span_range_map, LinearMap.range_eq_top.2 hπR]
  have hcomp : ∀ x, W.map π (W.map ι x) = 0 := fun x => by
    apply E.jD_inj
    rw [jD_map', jD_map', map_zero]
    exact hexR.apply_apply_eq_zero _
  refine ⟨fun x y hxy => E.jD_inj T (hιR ?_), fun y => ⟨fun hy => ?_, ?_⟩, hsurj⟩
  · rw [← jD_map', ← jD_map', hxy]
  · haveI := (W.DD_free Z).1
    obtain ⟨s, hs⟩ := (W.map π).exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hsurj)
    have hs' : ∀ z, W.map π (s z) = z := fun z => LinearMap.congr_fun hs z
    have htop : LinearMap.range (W.map ι) ⊔ LinearMap.range s = ⊤ := by
      refine eq_top_DD E hm Yt _ ?_
      set U := Submodule.span RW (E.jD Yt '' ((LinearMap.range (W.map ι) ⊔ LinearMap.range s :
        Submodule W.EE (W.DD Yt)) : Set (W.DD Yt))) with hU
      have hk : LinearMap.ker ((latMap π).baseChange RW) ≤ U := by
        rw [LinearMap.exact_iff.1 hexR, ← span_range_map E]
        exact Submodule.span_mono (Set.image_mono (SetLike.coe_subset_coe.2 le_sup_left))
      have hmap : U.map ((latMap π).baseChange RW) = ⊤ := by
        rw [eq_top_iff, ← E.jD_span Z, Submodule.span_le]
        rintro _ ⟨z, rfl⟩
        refine ⟨E.jD Yt (s z), Submodule.subset_span
          ⟨s z, Submodule.mem_sup_right ⟨z, rfl⟩, rfl⟩, ?_⟩
        rw [← jD_map', hs']
      have := Submodule.comap_map_eq ((latMap π).baseChange RW) U
      rw [hmap, Submodule.comap_top, sup_eq_left.2 hk] at this
      exact this.symm
    obtain ⟨_, ⟨t, rfl⟩, _, ⟨z, rfl⟩, rfl⟩ := Submodule.mem_sup.1 (htop ▸ Submodule.mem_top (x := y))
    rw [map_add, hcomp, hs', zero_add] at hy
    exact ⟨t, by rw [hy, map_zero, add_zero]⟩
  · rintro ⟨x, rfl⟩
    exact hcomp x

theorem map_ne_top_of_tie [IsNoetherianRing O]
    (hO : ∀ c : O, IsUnit c ∨ ∃ k : ℕ, (PD.p : O) ∣ c ^ k)
    (hsep : ∀ x : RW, (∀ k : ℕ, (PD.p : RW) ^ k ∣ x) → x = 0)
    (m : Ideal W.EE) (hm : m.IsMaximal) : m.map E.ioE.toRingHom ≠ ⊤ := by
  haveI := PD.finK₀
  haveI : NeZero n := ⟨by rw [W.n_eq]; exact Module.finrank_pos.ne'⟩
  haveI := W.EE_complete
  refine map_maximal_ne_top n PD.p hO (algebraMap (LetA O n) W.EE) W.EE_π (fun x => ?_) _
    (ioE_injective E) hsep m hm
  simpa using W.EE_dense x 1

end Generic

section Concrete

variable {l : ℕ} [Fact l.Prime]

theorem isUnit_or_dvd_pow (P : LocPrime l) (LL : FinExt l) (c : ↥(OL LL)) :
    IsUnit c ∨ ∃ k : ℕ, ((l : ℕ) : ↥(OL LL)) ∣ c ^ k := by
  by_cases hc0 : c = 0
  · exact Or.inr ⟨1, by simp [hc0]⟩
  have hc0' : (c : ↥LL.1) ≠ 0 := fun h => hc0 (Subtype.ext h)
  have hl0 : ((l : ℕ) : ↥LL.1) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hne : P.v LL c ≠ ⊤ := by simpa using hc0'
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 hne
  have hq0 : (0 : WithTop ℚ) ≤ q := hq ▸ (P.v_O LL c).2 c.2
  have hq0' : 0 ≤ q := by exact_mod_cast hq0
  rcases hq0'.eq_or_lt with h | h
  · left
    have hinv : (c : ↥LL.1)⁻¹ ∈ OL LL := by
      rw [← P.v_O, AddValuation.map_inv, ← hq, ← h]
      simp
    exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hc0')⟩
  · right
    obtain ⟨k, hk⟩ := Archimedean.arch (1 : ℚ) h
    have hmem : (c : ↥LL.1) ^ k / (l : ↥LL.1) ∈ OL LL := by
      rw [← P.v_O, AddValuation.map_div, AddValuation.map_pow, P.v_l, ← hq]
      have : (k • (q : WithTop ℚ) - 1 : WithTop ℚ) = ((k • q - 1 : ℚ) : WithTop ℚ) := by
        norm_cast
      rw [this]
      exact_mod_cast sub_nonneg.2 hk
    refine ⟨k, ⟨_, hmem⟩, Subtype.ext ?_⟩
    simp only [SubmonoidClass.coe_pow, MulMemClass.coe_mul, SubringClass.coe_natCast]
    rw [mul_div_cancel₀ _ hl0]

theorem finite_OL (LL : FinExt l) : Module.Finite ℤ_[l] ↥(OL LL) :=
  haveI := LL.2
  IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)

theorem free_OL (LL : FinExt l) : Module.Free ℤ_[l] ↥(OL LL) :=
  haveI := LL.2
  haveI : Module.IsTorsionFree ℤ_[l] ↥LL.1 :=
    Module.IsTorsionFree.trans_faithfulSMul ℤ_[l] ℚ_[l] ↥LL.1
  IsIntegralClosure.module_free ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)

theorem sep_WCb (x : WCb l) (hx : ∀ k : ℕ, (l : WCb l) ^ k ∣ x) : x = 0 := by
  ext i
  obtain ⟨y, hy⟩ := hx (i + 1)
  rw [hy, mul_comm, WittVector.mul_pow_charP_coeff_zero y (Nat.lt_succ_self i)]
  simp

theorem sep_RW (LL : FinExt l) (x : RW LL) (hx : ∀ k : ℕ, (l : RW LL) ^ k ∣ x) : x = 0 := by
  classical
  haveI := free_OL LL
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := WCb l)
    (Module.Free.chooseBasis ℤ_[l] ↥(OL LL))
  apply e.injective
  rw [map_zero]
  ext i : 1
  refine sep_WCb _ fun k => ?_
  obtain ⟨y, hy⟩ := hx k
  refine ⟨e y i, ?_⟩
  rw [hy, ← Nat.cast_pow, ← nsmul_eq_mul, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul, Nat.cast_pow]

end Concrete

theorem DD_exact : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm9 D HW F → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T Yt Z : LocLat S.G S.Qp S.LL S.O) (ι : LatHom T.L Yt.L) (π : LatHom Yt.L Z.L), IsSESLat (Qp := S.Qp) ι π → Function.Injective (S.W.map ι) ∧ Function.Exact (S.W.map ι) (S.W.map π) ∧ Function.Surjective (S.W.map π) := by
  intro D HW F _ l _ K s LL h S E T Yt Z ι π hses
  haveI := finite_OL LL
  haveI : IsNoetherianRing ↥(OL LL) := IsNoetherianRing.of_finite ℤ_[l] ↥(OL LL)
  haveI : IsNoetherianRing S.O := this
  have hp : S.PD.p = l := (D.loc l).PD_p K
  refine exact_of_tie E (map_ne_top_of_tie E ?_ ?_) T Yt Z ι π hses
  · rw [hp]
    exact isUnit_or_dvd_pow (D.loc l) LL
  · rw [hp]
    exact sep_RW LL

end GlobalTheory.EtaleExact
