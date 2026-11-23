import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsGlue
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.GlueCoherence
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

variable {X : Scheme.{0}}

lemma mul_not_mem_prime_iff {P : Ideal ℤ} (hP : P.IsPrime) (a b : ℤ) :
    a * b ∉ P ↔ a ∉ P ∧ b ∉ P := by
  rw [hP.mul_mem_iff_mem_or_mem, not_or]

lemma invOpen_mul_eq_inf (f : X ⟶ SpecZ) (a b : ℤ) :
    invOpen f (a * b) = invOpen f a ⊓ invOpen f b := by
  ext x
  change a * b ∉ _ ↔ a ∉ _ ∧ b ∉ _
  exact mul_not_mem_prime_iff (PrimeSpectrum.isPrime _) a b

lemma invOpen_le_of_dvd' (f : X ⟶ SpecZ) {a b : ℤ} (h : a ∣ b) : invOpen f b ≤ invOpen f a := by
  obtain ⟨c, rfl⟩ := h
  exact invOpen_mul_le_left f a c

lemma not_dvd_prod_erase (S : Finset Nat.Primes) (p : Nat.Primes) :
    ¬ (p : ℕ) ∣ ∏ q ∈ S.erase p, (q : ℕ) := by
  intro h
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff p.2.prime _).1 h
  have : p = q := Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.2 q.2).1 hpq)
  subst this
  exact Finset.notMem_erase _ _ hq

lemma primeProd_eq_cast (S : Finset Nat.Primes) :
    primeProd S = ((∏ q ∈ S, (q : ℕ) : ℕ) : ℤ) := by
  simp [primeProd]

theorem GlueBundles.localPiece (hSB : SpreadBundle.Statement) (hSI : SpreadIso.Statement)
    (hVR : VectorBundleRestrict.Statement) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f]
    (S : Finset Nat.Primes) (E₀ : (invOpen f (primeProd S) : Scheme.{0}).Modules)
    (hE₀ : IsVectorBundle E₀) (p : S) (Ep : (baseChange f (ZLoc p)).Modules) (hEp : IsVectorBundle Ep)
    (β : (Scheme.Modules.pullback (ratToLoc f p)).obj Ep ≅
      (Scheme.Modules.pullback (toInvOpen f ℚ (primeProd S)
        (isUnit_intCast_rat _ (primeProd_ne_zero S)))).obj E₀) :
    ∃ (n : ℕ) (hn : ¬ (((p : Nat.Primes) : ℕ) : ℤ) ∣ (n : ℤ)),
      (∀ q ∈ S, q ≠ (p : Nat.Primes) → ((q : ℕ) : ℤ) ∣ (n : ℤ)) ∧
      ∃ (F : (invOpen f n : Scheme.{0}).Modules), IsVectorBundle F ∧
      ∃ (ψ' : (Scheme.Modules.pullback (X.homOfLE
            (inf_le_left : invOpen f n ⊓ invOpen f (primeProd S) ≤ invOpen f n))).obj F ≅
          (Scheme.Modules.pullback (X.homOfLE
            (inf_le_right : invOpen f n ⊓ invOpen f (primeProd S) ≤ invOpen f (primeProd S)))).obj E₀)
        (δ : (Scheme.Modules.pullback (toInvOpen f (ZLoc p) n (isUnit_intCast_zLoc p n hn))).obj F ≅ Ep),
      ∀ (E : X.Modules) (e₀ : (Scheme.Modules.pullback (invOpen f (primeProd S)).ι).obj E ≅ E₀)
        (eU : (Scheme.Modules.pullback (invOpen f n).ι).obj E ≅ F),
        pullbackCompIso (X.homOfLE_ι (inf_le_right :
            invOpen f n ⊓ invOpen f (primeProd S) ≤ invOpen f (primeProd S))) e₀ =
          pullbackCompIso (X.homOfLE_ι (inf_le_left :
            invOpen f n ⊓ invOpen f (primeProd S) ≤ invOpen f n)) eU ≪≫ ψ' →
        pullbackCompIso (toInvOpen_ι f ℚ (primeProd S)
            (isUnit_intCast_rat _ (primeProd_ne_zero S))) e₀ =
          pullbackCompIso (ratToLoc_baseChangeMap f p)
            (pullbackCompIso (toInvOpen_ι f (ZLoc p) n (isUnit_intCast_zLoc p n hn)) eU ≪≫ δ) ≪≫ β := by
  classical
  obtain ⟨pp, hpS⟩ := p
  obtain ⟨m₀, hm₀pos, hpm₀, hspread⟩ := hSB X f pp Ep hEp
  set M : ℕ := ∏ q ∈ S, (q : ℕ) with hMdef
  set N : ℕ := m₀ * ∏ q ∈ S.erase pp, (q : ℕ) with hNdef
  have hpNnat : ¬ (pp : ℕ) ∣ N := fun h =>
    ((Nat.Prime.dvd_mul pp.2).1 h).elim hpm₀ (not_dvd_prod_erase S pp)
  have hpN : ¬ ((pp : ℕ) : ℤ) ∣ (N : ℤ) := by exact_mod_cast hpNnat
  obtain ⟨E', hE', ⟨σ⟩⟩ := hspread N (dvd_mul_right _ _) hpN
  have hMpos : 0 < M := Finset.prod_pos fun q _ => q.2.pos
  have hNpos : 0 < N := Nat.mul_pos hm₀pos (Finset.prod_pos fun q _ => q.2.pos)
  set a : ℕ := N * M with hadef
  have ha : 0 < a := Nat.mul_pos hNpos hMpos
  have hm : primeProd S = (M : ℤ) := primeProd_eq_cast S
  have haN : invOpen f (a : ℤ) ≤ invOpen f (N : ℤ) :=
    invOpen_le_of_dvd' f (by exact_mod_cast dvd_mul_right N M)
  have haM : invOpen f (a : ℤ) ≤ invOpen f (primeProd S) := by
    rw [hm]
    exact invOpen_le_of_dvd' f (by exact_mod_cast dvd_mul_left M N)
  have hFa : IsVectorBundle ((Scheme.Modules.pullback (X.homOfLE haN)).obj E') :=
    hVR _ _ (X.homOfLE haN) E' hE'
  have hGa : IsVectorBundle ((Scheme.Modules.pullback (X.homOfLE haM)).obj E₀) :=
    hVR _ _ (X.homOfLE haM) E₀ hE₀
  have uQa : IsUnit ((a : ℤ) : ℚ) := isUnit_intCast_rat a (by exact_mod_cast ha.ne')
  have uQm : IsUnit ((primeProd S : ℤ) : ℚ) := isUnit_intCast_rat _ (primeProd_ne_zero S)
  have uPN : IsUnit ((N : ℤ) : ZLoc pp) := isUnit_intCast_zLoc pp N hpN
  have uQN : IsUnit ((N : ℤ) : ℚ) := isUnit_intCast_rat N (by exact_mod_cast hNpos.ne')
  have e1 : toInvOpen f ℚ a uQa ≫ X.homOfLE haN = ratToLoc f pp ≫ toInvOpen f (ZLoc pp) N uPN := by
    rw [toInvOpen_homOfLE f ℚ uQa uQN haN, ← cancel_mono (invOpen f N).ι, Category.assoc,
      toInvOpen_ι, toInvOpen_ι, ratToLoc_baseChangeMap]
  have e2 : toInvOpen f ℚ a uQa ≫ X.homOfLE haM = toInvOpen f ℚ (primeProd S) uQm :=
    toInvOpen_homOfLE f ℚ uQa uQm haM
  obtain ⟨m', hm', ψ, hψ⟩ := hSI X f a ha _ _ hFa hGa
    ((pullbackCompIso e1 (Iso.refl ((Scheme.Modules.pullback (X.homOfLE haN)).obj E'))).symm ≪≫
      pullbackCompIso (rfl : ratToLoc f pp ≫ toInvOpen f (ZLoc pp) N uPN = _) σ ≪≫ β ≪≫
      pullbackCompIso e2 (Iso.refl ((Scheme.Modules.pullback (X.homOfLE haM)).obj E₀)))
  obtain ⟨k, m'', hpm'', hm'eq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm'.ne' (pp : ℕ) pp.2.one_lt.ne'
  set n : ℕ := N * m'' with hndef
  have hpn : ¬ ((pp : ℕ) : ℤ) ∣ (n : ℤ) := by
    have : ¬ (pp : ℕ) ∣ n := fun h => ((Nat.Prime.dvd_mul pp.2).1 h).elim hpNnat hpm''
    exact_mod_cast this
  have hqn : ∀ q ∈ S, q ≠ pp → ((q : ℕ) : ℤ) ∣ (n : ℤ) := by
    intro q hq hne
    have : (q : ℕ) ∣ n := Dvd.dvd.mul_right (Dvd.dvd.mul_left
      (Finset.dvd_prod_of_mem (fun r : Nat.Primes => (r : ℕ)) (Finset.mem_erase.2 ⟨hne, hq⟩)) _) _
    exact_mod_cast this
  have hUN : invOpen f (n : ℤ) ≤ invOpen f (N : ℤ) :=
    invOpen_le_of_dvd' f (by exact_mod_cast dvd_mul_right N m'')
  have hF : IsVectorBundle ((Scheme.Modules.pullback (X.homOfLE hUN)).obj E') :=
    hVR _ _ (X.homOfLE hUN) E' hE'
  have hWam : invOpen f n ⊓ invOpen f (primeProd S) ≤ invOpen f ((a : ℤ) * (m' : ℤ)) := by
    rintro x ⟨hxU, hxV⟩
    have hP := PrimeSpectrum.isPrime (f.base x)
    change (n : ℤ) ∉ (f.base x).asIdeal at hxU
    change primeProd S ∉ (f.base x).asIdeal at hxV
    change (a : ℤ) * (m' : ℤ) ∉ (f.base x).asIdeal
    rw [hm] at hxV
    rw [hndef, Nat.cast_mul, mul_not_mem_prime_iff hP] at hxU
    have hpP : ((pp : ℕ) : ℤ) ∉ (f.base x).asIdeal := fun h => hxV (by
      obtain ⟨c, hc⟩ : ((pp : ℕ) : ℤ) ∣ (M : ℤ) := by
        exact_mod_cast Finset.dvd_prod_of_mem (fun q : Nat.Primes => (q : ℕ)) hpS
      rw [hc]
      exact Ideal.mul_mem_right _ _ h)
    have hk : ((pp : ℕ) : ℤ) ^ k ∉ (f.base x).asIdeal := fun h => hpP (hP.mem_of_pow_mem k h)
    rw [hadef, hm'eq]
    push_cast
    rw [mul_not_mem_prime_iff hP, mul_not_mem_prime_iff hP, mul_not_mem_prime_iff hP]
    exact ⟨⟨hxU.1, hxV⟩, hk, hxU.2⟩
  have e7 : (X.homOfLE hWam ≫ X.homOfLE (invOpen_mul_le_left f a m')) ≫ X.homOfLE haN =
      X.homOfLE (inf_le_left : invOpen f n ⊓ invOpen f (primeProd S) ≤ invOpen f n) ≫
        X.homOfLE hUN := by
    simp only [Scheme.homOfLE_homOfLE]
  have e8 : (X.homOfLE hWam ≫ X.homOfLE (invOpen_mul_le_left f a m')) ≫ X.homOfLE haM =
      X.homOfLE (inf_le_right : invOpen f n ⊓ invOpen f (primeProd S) ≤ invOpen f (primeProd S)) := by
    simp only [Scheme.homOfLE_homOfLE]
  have uPn : IsUnit ((n : ℤ) : ZLoc pp) := isUnit_intCast_zLoc pp n hpn
  have h5 : toInvOpen f (ZLoc pp) n uPn ≫ X.homOfLE hUN = toInvOpen f (ZLoc pp) N uPN :=
    toInvOpen_homOfLE f _ uPn uPN hUN
  refine ⟨n, hpn, hqn, _, hF, starIso rfl e7 e8 ψ,
    (pullbackCompIso h5 (Iso.refl ((Scheme.Modules.pullback (X.homOfLE hUN)).obj E'))).symm ≪≫ σ, ?_⟩
  intro E e₀ eU hglue
  have hm''0 : m'' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm'eq
    omega
  have hnm : ((n : ℤ) * primeProd S : ℤ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (Nat.mul_pos hNpos
      (Nat.pos_of_ne_zero hm''0)).ne') (primeProd_ne_zero S)
  have hrange : Set.range (baseChangeMap f ℚ) ⊆
      Set.range (invOpen f n ⊓ invOpen f (primeProd S)).ι := by
    intro y hy
    have := range_baseChangeMap_subset f ℚ ((n : ℤ) * primeProd S) (isUnit_intCast_rat _ hnm) hy
    rw [Scheme.Opens.range_ι] at this ⊢
    rwa [invOpen_mul_eq_inf] at this
  have qW : IsOpenImmersion.lift _ _ hrange ≫ (invOpen f n ⊓ invOpen f (primeProd S)).ι =
      baseChangeMap f ℚ := IsOpenImmersion.lift_fac _ _ _
  have qV : IsOpenImmersion.lift _ _ hrange ≫ X.homOfLE (inf_le_right :
      invOpen f n ⊓ invOpen f (primeProd S) ≤ invOpen f (primeProd S)) =
      toInvOpen f ℚ (primeProd S) uQm := by
    rw [← cancel_mono (invOpen f (primeProd S)).ι, Category.assoc, Scheme.homOfLE_ι, qW, toInvOpen_ι]
  have qU : IsOpenImmersion.lift _ _ hrange ≫ X.homOfLE (inf_le_left :
      invOpen f n ⊓ invOpen f (primeProd S) ≤ invOpen f n) =
      ratToLoc f pp ≫ toInvOpen f (ZLoc pp) n uPn := by
    rw [← cancel_mono (invOpen f n).ι, Category.assoc, Scheme.homOfLE_ι, qW, Category.assoc,
      toInvOpen_ι, ratToLoc_baseChangeMap]
  have qt : IsOpenImmersion.lift _ _ hrange ≫ X.homOfLE hWam =
      toInvOpen f ℚ ((a : ℤ) * (m' : ℤ)) (isUnit_intCast_rat ((a : ℤ) * m') (by positivity)) := by
    rw [← cancel_mono (invOpen f ((a : ℤ) * (m' : ℤ))).ι, Category.assoc, Scheme.homOfLE_ι, qW,
      toInvOpen_ι]
  exact glue_compat_chase (X.homOfLE_ι _) (X.homOfLE_ι _) (toInvOpen_ι f ℚ _ _)
    (ratToLoc_baseChangeMap f pp) (toInvOpen_ι f (ZLoc pp) n uPn) h5 e1 e2
    (toInvOpen_homOfLE f ℚ _ _ _) rfl e7 e8 qV qU qt qW e₀ eU σ β ψ hψ hglue

theorem GlueBundles.proof (hSB : SpreadBundle.Statement) (hSI : SpreadIso.Statement)
    (hPC : PrimeOpensCover.Statement) (hGS : GlueModulesStar.Statement)
    (hVR : VectorBundleRestrict.Statement) (hVL : VectorBundleLocal.Statement) :
    GlueBundles.Statement := by
  classical
  intro X f _ _ S E₀ Ep hE₀ hEp β
  have key := fun p : S => GlueBundles.localPiece hSB hSI hVR f S E₀ hE₀ p (Ep p) (hEp p) (β p)
  choose n hn hqdiv F hF ψ' δ hcompat using key
  let mp : Nat.Primes → ℤ := fun q => if h : q ∈ S then (n ⟨q, h⟩ : ℤ) else 1
  have hmp : ∀ p : S, mp p = (n p : ℤ) := fun p => dif_pos p.2
  obtain ⟨hcover, hpair⟩ := hPC X f S mp
    (fun p hp => by rw [show mp p = (n ⟨p, hp⟩ : ℤ) from dif_pos hp]; exact hn ⟨p, hp⟩)
    (fun p hp q hq hqp => by
      rw [show mp p = (n ⟨p, hp⟩ : ℤ) from dif_pos hp]
      exact hqdiv ⟨p, hp⟩ q hq hqp)
  let U : S → X.Opens := fun p => invOpen f (n p)
  have hUsup : (⨆ q ∈ S, invOpen f (mp q)) = ⨆ p : S, U p := by
    rw [iSup_subtype']
    exact iSup_congr fun p => by rw [hmp]
  have hcov : invOpen f (primeProd S) ⊔ ⨆ p : S, U p = ⊤ := by
    rw [← hUsup]
    exact hcover
  have hpairU : ∀ i j : S, i ≠ j → U i ⊓ U j ≤ invOpen f (primeProd S) := by
    intro i j hij
    have := (hpair i i.2 j j.2 (fun h => hij (Subtype.ext h))).1
    rwa [hmp, hmp] at this
  obtain ⟨E, e₀, e, hglue⟩ := hGS X (invOpen f (primeProd S)) S U hcov hpairU E₀ F ψ'
  have hVB : IsVectorBundle E := by
    refine hVL X (Option S) (fun o => o.elim (invOpen f (primeProd S)) U) ?_ E ?_
    · rw [iSup_option]
      exact hcov
    · intro o
      cases o with
      | none => exact hE₀.of_iso e₀.symm
      | some p => exact (hF p).of_iso (e p).symm
  exact ⟨E, hVB, e₀, fun p => pullbackCompIso (toInvOpen_ι f (ZLoc p) (n p)
      (isUnit_intCast_zLoc p (n p) (hn p))) (e p) ≪≫ δ p,
    fun p => hcompat p E e₀ (e p) (hglue p)⟩

end

end GroundTheory.Heights₂.Heights.Model
