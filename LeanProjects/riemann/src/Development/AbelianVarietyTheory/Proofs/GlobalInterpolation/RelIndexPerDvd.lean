import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT.IdxBound

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem mem_of_locP {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (M : Submodule (𝓞 E) W) (x : W)
    (h : ∀ Q : HeightOneSpectrum (𝓞 E), x ∈ localization₂ Q.asIdeal M) : x ∈ M := by
  by_contra hx
  let I : Ideal (𝓞 E) := M.comap (LinearMap.toSpanSingleton (𝓞 E) W x)
  have hI : ∀ s, s ∈ I ↔ s • x ∈ M := fun s => Iff.rfl
  have hne : I ≠ ⊤ := fun e => hx (by simpa using (hI 1).1 (e ▸ Submodule.mem_top))
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I hne
  have hm0 : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)
  obtain ⟨s, hs, hsx⟩ := (mem_locP ⟨m, hm.isPrime, hm0⟩ M x).1 (h _)
  exact hs (hle ((hI s).2 hsx))

theorem mem_localization_of_smul_mem {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) W)
    {x : W} {s : 𝓞 E} (hs : s ∉ P.asIdeal) (h : s • x ∈ localization₂ P.asIdeal M) : x ∈ localization₂ P.asIdeal M := by
  obtain ⟨t, ht, htx⟩ := (mem_locP P M _).1 h
  refine (mem_locP P M _).2 ⟨t * s, fun h' => (P.isPrime.mem_or_mem h').elim ht hs, ?_⟩
  rwa [mul_smul]

theorem per_apply_mem {AA : Submodule (𝓞 E) E} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}
    {P : HeightOneSpectrum (𝓞 E)} (hA : localization₂ P.asIdeal AA = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E))
    {y : HomE E a b} (hy : y ∈ perO AA N N') {v : Sp E a} (hv : v ∈ localization₂ P.asIdeal N) : y v ∈ localization₂ P.asIdeal N' := by
  obtain ⟨s', hs', hv'⟩ := (mem_locP P N v).1 hv
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, hr, x, hx, rfl⟩ := hz
    obtain ⟨s, hs, hr'⟩ := (mem_locP P _ r).1 (hA ▸ le_locP P AA hr)
    obtain ⟨t, ht⟩ := Submodule.mem_one.1 hr'
    refine mem_localization_of_smul_mem P _ hs (mem_localization_of_smul_mem P _ hs' (le_locP P _ ?_))
    have h1 : x (s' • v) ∈ N' := hx _ hv'
    have h2 : s' • s • (r • x) v = t • x (s' • v) := by
      rw [LinearMap.map_smul_of_tower, LinearMap.smul_apply, ← smul_assoc s r, ← ht, algebraMap_smul, smul_comm]
    rw [h2]
    exact N'.smul_mem t h1
  | zero => simp
  | add y z _ _ hy hz => simpa using add_mem hy hz
  | smul r z _ hz => simpa using Submodule.smul_mem _ r hz

theorem mem_localization_perO {AA : Submodule (𝓞 E) E} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}
    {P : HeightOneSpectrum (𝓞 E)} (hA : localization₂ P.asIdeal AA = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)) (hN : N.FG)
    {y : HomE E a b} (hy : ∀ v ∈ N, y v ∈ localization₂ P.asIdeal N') : y ∈ localization₂ P.asIdeal (perO AA N N') := by
  classical
  obtain ⟨S, rfl⟩ := hN
  choose! s hs hsy using fun v (hv : v ∈ S) => (mem_locP P N' _).1 (hy v (Submodule.subset_span hv))
  have hP : ∏ v ∈ S, s v ∉ P.asIdeal := fun h => by
    obtain ⟨v, hv, h'⟩ := (P.isPrime.prod_mem_iff).1 h
    exact hs v hv h'
  have hh : (∏ v ∈ S, s v) • y ∈ homO (Submodule.span (𝓞 E) (S : Set (Sp E a))) N' := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      rw [← Finset.prod_erase_mul S s hv, LinearMap.smul_apply, mul_smul]
      exact N'.smul_mem _ (hsy v hv)
    | zero => simp
    | add v w _ _ hv hw => rw [map_add]; exact add_mem hv hw
    | smul r v _ hv => rw [LinearMap.map_smul_of_tower]; exact N'.smul_mem r hv
  obtain ⟨t, ht, h1⟩ := (mem_locP P AA 1).1 (hA ▸ le_locP P _ (Submodule.one_le.1 le_rfl))
  refine mem_localization_of_smul_mem P _ hP (mem_localization_of_smul_mem P _ ht (le_locP P _ (Submodule.subset_span ⟨_, h1, _, hh, ?_⟩)))
  rw [smul_assoc t (1 : E), one_smul]

theorem smul_mem_per {AA : Submodule (𝓞 E) E} {N : Submodule (𝓞 E) (Sp E a)} {N' N'' : Submodule (𝓞 E) (Sp E b)}
    {w : 𝓞 E} (h : ∀ y ∈ N', (w : E) • y ∈ N'') {y : HomE E a b} (hy : y ∈ perO AA N N') : w • y ∈ perO AA N N'' := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, hr, x, hx, rfl⟩ := hz
    refine Submodule.subset_span ⟨r, hr, w • x, fun v hv => h _ (hx v hv), (smul_comm _ _ _).symm⟩
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | smul r z _ hz => rw [smul_comm]; exact Submodule.smul_mem _ r hz

theorem apply_mem_of_std {N' : Submodule (𝓞 E) (Sp E b)} {P : HeightOneSpectrum (𝓞 E)} {y : HomE E a b}
    (hy : ∀ i, y (Pi.single i 1) ∈ localization₂ P.asIdeal N') {v : Sp E a} (hv : v ∈ stdAt E a P) : y v ∈ localization₂ P.asIdeal N' := by
  obtain ⟨s, hs, hsv⟩ := (mem_locP P _ v).1 hv
  choose t ht using fun i => Submodule.mem_one.1 (Submodule.mem_pi.1 hsv i (Set.mem_univ _))
  refine mem_localization_of_smul_mem P _ hs ?_
  have e : s • v = ∑ i, t i • (Pi.single i 1 : Sp E a) := by
    ext j
    rw [← ht j]
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  rw [← LinearMap.map_smul_of_tower, e, map_sum]
  exact Submodule.sum_mem _ fun i _ => by
    rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ _ (hy i)

theorem relIndex_per_dvd : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (p : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (d : DecoSet X.E b (divs ϖ) SG) (N'' : Submodule (𝓞 X.E) (Sp X.E b)), A.AA.FG → A.AA ≠ ⊥ → A.AAUnit (divs ϖ) → ϖ ≠ 0 → (∀ P ∈ divs ϖ, Ideal.absNorm P.asIdeal = p) → IsSdLat N → IsSdLat N'' → (∀ P ∈ divs ϖ, localization₂ P.asIdeal N = stdAt X.E a P) → ((∀ y ∈ d.1.N, (ϖ : X.E) • y ∈ N'') ∧ (∀ y ∈ N'', star (ϖ : X.E) • y ∈ d.1.N) ∧ ∀ (P : ↥(divs ϖ)) (y : Sp X.E b), y ∈ localization₂ P.1.asIdeal N'' ↔ y ∈ d.1.at P.1 ∧ d.1.f P y = 0) → (per A N N'').toAddSubgroup.relIndex (per A N d.1.N).toAddSubgroup ∣ p ^ ((divs ϖ).card * a) := by
  intro X A a b SG ϖ p N d N'' _ _ hU h0 hp hN _ hstd ⟨h1, _, h3⟩
  have he : ∀ (P : ↥(divs ϖ)) (i : Fin a), (Pi.single i 1 : Sp X.E a) ∈ localization₂ P.1.asIdeal N := fun P i => by
    rw [hstd P.1 P.2]
    exact le_locP P.1 _ (by simpa using single_mem_stdLat (E := X.E) i 1)
  have hm : ∀ (x : (per A N d.1.N).toAddSubgroup) (P : ↥(divs ϖ)) (i : Fin a), x.1 (Pi.single i 1) ∈ d.1.at P.1 :=
    fun x P i => per_apply_mem (hU P.1 P.2) x.2 (he P i)
  let φ : (per A N d.1.N).toAddSubgroup →+ ((P : ↥(divs ϖ)) → Fin a → 𝓞 X.E ⧸ P.1.asIdeal) :=
    AddMonoidHom.mk' (fun x P i => d.1.f P (x.1 (Pi.single i 1))) fun x y => by
      funext P i
      exact d.2.f_add P _ (hm x P i) _ (hm y P i)
  have hker : φ.ker ≤ (per A N N'').toAddSubgroup.addSubgroupOf (per A N d.1.N).toAddSubgroup := by
    intro x hx
    refine mem_of_locP (per A N N'') x.1 fun Q => ?_
    by_cases hQ : Q ∈ divs ϖ
    · refine mem_localization_perO (hU Q hQ) hN.1.fg fun v hv => apply_mem_of_std (fun i => ?_) (hstd Q hQ ▸ le_locP Q N hv)
      exact (h3 ⟨Q, hQ⟩ _).2 ⟨hm x ⟨Q, hQ⟩ i, congrFun (congrFun hx ⟨Q, hQ⟩) i⟩
    · exact mem_localization_of_smul_mem Q _ (fun h => hQ ((mem_divs h0 Q).2 h)) (le_locP Q _ (smul_mem_per h1 x.2))
  have hc : Nat.card ((P : ↥(divs ϖ)) → Fin a → 𝓞 X.E ⧸ P.1.asIdeal) = p ^ ((divs ϖ).card * a) := by
    have : ∀ P : ↥(divs ϖ), Nat.card (Fin a → 𝓞 X.E ⧸ P.1.asIdeal) = p ^ a := fun P => by
      rw [Nat.card_fun, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hp P.1 P.2]
      simp
    rw [Nat.card_pi, Finset.prod_congr rfl fun P _ => this P]
    simp [← pow_mul, mul_comm]
  refine (AddSubgroup.index_dvd_of_le hker).trans ?_
  rw [AddSubgroup.index_ker, ← hc]
  exact AddSubgroup.card_addSubgroup_dvd_card _

end GlobalTheory.MomT.IdxBound
