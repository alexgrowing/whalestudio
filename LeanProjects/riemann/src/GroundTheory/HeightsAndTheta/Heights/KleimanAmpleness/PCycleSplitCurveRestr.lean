import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CycleSplitCurveRestrSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationPoint
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsMemSupport
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace CycleSplit.Curve.Restr

section Cocycle

variable {n : ℕ} {U : Finset (Fin n)} {R : Type*} [CommRing R]
  {G : Cell U → Type*} [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)]
  {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}

theorem cocycle_res_eq {s : Cech.Cochain G 0} (hs : Cech.d G ρ 0 s = 0) (Ka Kb : Cech.Idx U 0)
    (J : Cech.Idx U 1) (hKa : Ka.1.1 ⊆ J.1.1) (hKb : Kb.1.1 ⊆ J.1.1) (hne : Ka.1.1 ≠ Kb.1.1) :
    ρ Ka.1 J.1 hKa (s Ka) = ρ Kb.1 J.1 hKb (s Kb) := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp Ka.2
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp Kb.2
  have hab : a ≠ b := fun h => hne (by rw [ha, hb, h])
  have haJ : a ∈ J.1.1 := hKa (by rw [ha]; exact Finset.mem_singleton_self a)
  have hbJ : b ∈ J.1.1 := hKb (by rw [hb]; exact Finset.mem_singleton_self b)
  have hJ : J.1.1 = {a, b} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact haJ
      · rw [Finset.mem_singleton.mp hz]; exact hbJ
    · have := J.2
      rw [Finset.card_pair hab]
      omega
  have fa : Cech.face J ⟨a, haJ⟩ = Kb := Subtype.ext (Subtype.ext (by
    change J.1.1.erase a = _
    rw [hJ, hb]
    exact Finset.erase_insert (by simpa using hab)))
  have fb : Cech.face J ⟨b, hbJ⟩ = Ka := Subtype.ext (Subtype.ext (by
    change J.1.1.erase b = _
    rw [hJ, ha, Finset.pair_comm]
    exact Finset.erase_insert (by simpa using Ne.symm hab)))
  have hval : ∀ L L' : Cech.Idx U 0, L = L' → ∀ (h : L.1.1 ⊆ J.1.1) (h' : L'.1.1 ⊆ J.1.1),
      ρ L.1 J.1 h (s L) = ρ L'.1 J.1 h' (s L') := by
    rintro L L' rfl h h'
    rfl
  have huniv : (Finset.univ : Finset J.1.1) = {⟨a, haJ⟩, ⟨b, hbJ⟩} := by
    ext ⟨z, hz⟩
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, true_iff]
    rw [hJ] at hz
    exact (Finset.mem_insert.mp hz).imp id Finset.mem_singleton.mp
  have hne' : (⟨a, haJ⟩ : J.1.1) ≠ ⟨b, hbJ⟩ := fun h => hab (congrArg Subtype.val h)
  have h0 := congrFun hs J
  rw [Cech.d_apply, Pi.zero_apply, huniv, Finset.sum_pair hne'] at h0
  rw [hval _ Kb fa _ hKb, hval _ Ka fb _ hKa] at h0
  have hsum : Cech.sgn J.1.1 a + Cech.sgn J.1.1 b = 0 := by
    have := Cech.sum_sgn_of_card_two J.2
    rw [← Finset.sum_coe_sort J.1.1, huniv, Finset.sum_pair hne'] at this
    exact this
  have hb2 : Cech.sgn J.1.1 b = - Cech.sgn J.1.1 a := by linarith
  rw [hb2, neg_smul, ← sub_eq_add_neg, ← smul_sub] at h0
  have hsq : Cech.sgn J.1.1 a * Cech.sgn J.1.1 a = 1 := by
    unfold Cech.sgn; rw [← mul_pow]; norm_num
  have h2 : ρ Kb.1 J.1 hKb (s Kb) - ρ Ka.1 J.1 hKa (s Ka) = 0 := by
    rw [← one_smul ℤ (ρ Kb.1 J.1 hKb (s Kb) - ρ Ka.1 J.1 hKa (s Ka)), ← hsq, mul_smul, h0, smul_zero]
  exact (sub_eq_zero.mp h2).symm

end Cocycle

section H0

variable {n : ℕ} {U : Finset (Fin n)} {R : Type*} [CommRing R]
  {G : Cell U → Type*} [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)]
  {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}
  {M : Type*} [AddCommGroup M] [Module R M] (π : ∀ I : Cell U, M →ₗ[R] G I)

def constK : M →ₗ[R] Cech.Cochain G 0 where
  toFun m K := π K.1 m
  map_add' a b := funext fun K => map_add (π K.1) a b
  map_smul' c a := funext fun K => map_smul (π K.1) c a

variable (hπ : ∀ I J h m, ρ I J h (π I m) = π J m)

include hπ in
theorem constK_cocycle (m : M) : Cech.d G ρ 0 (constK π m) = 0 :=
  Cech.d_zero_of_compat (v := fun I => π I m) (fun I J h => hπ I J h m)

def toH0 : M →ₗ[R] Cech.H G ρ 0 :=
  (Submodule.mkQ _).comp ((constK π).codRestrict (LinearMap.ker (Cech.d G ρ 0))
    fun m => LinearMap.mem_ker.mpr (constK_cocycle π hπ m))

theorem toH0_eq_zero_iff_components (m : M) : toH0 π hπ m = 0 ↔ ∀ K : Cech.Idx U 0, π K.1 m = 0 := by
  change (Submodule.Quotient.mk ⟨constK π m, LinearMap.mem_ker.mpr (constK_cocycle π hπ m)⟩ :
    LinearMap.ker (Cech.d G ρ 0) ⧸ (Cech.bdry G ρ 0).comap (LinearMap.ker (Cech.d G ρ 0)).subtype) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  change (constK π m) ∈ (⊥ : Submodule R (Cech.Cochain G 0)) ↔ _
  rw [Submodule.mem_bot]
  constructor
  · intro h K
    exact congrFun h K
  · intro h
    funext K
    exact h K

theorem toH0_surjective_of_lift
    (hlift : ∀ s : Cech.Cochain G 0, Cech.d G ρ 0 s = 0 → ∃ m : M, ∀ K : Cech.Idx U 0, π K.1 m = s K) :
    Function.Surjective (toH0 π hπ) := by
  intro z
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨m, hm⟩ := hlift s.1 (LinearMap.mem_ker.mp s.2)
  refine ⟨m, ?_⟩
  change (Submodule.Quotient.mk ⟨constK π m, LinearMap.mem_ker.mpr (constK_cocycle π hπ m)⟩ :
    LinearMap.ker (Cech.d G ρ 0) ⧸ (Cech.bdry G ρ 0).comap (LinearMap.ker (Cech.d G ρ 0)).subtype) =
      Submodule.Quotient.mk s
  congr 1
  exact Subtype.ext (funext hm)

end H0

section Quot

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

def secsIncl (F : SubSystem S x Ω) (I : Chart x) : F.secs →ₗ[S] F.sub I where
  toFun z := ⟨z, CechZerothCohomologySections.mem_sub_of_mem_secs F z.2 I⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def quotPi (F G : SubSystem S x Ω) (I : Chart x) : F.secs →ₗ[S] F.sub I ⧸ SubSystem.quotSub F G I :=
  (SubSystem.quotSub F G I).mkQ.comp (secsIncl F I)

theorem quotPi_res (F G : SubSystem S x Ω) (I J : Chart x) (h : I.1 ⊆ J.1) (z : F.secs) :
    SubSystem.quotRes F G I J h (quotPi F G I z) = quotPi F G J z := rfl

theorem quotPi_eq_zero_iff (F G : SubSystem S x Ω) (I : Chart x) (z : F.secs) :
    quotPi F G I z = 0 ↔ (z : Ω) ∈ G.sub I := by
  change Submodule.Quotient.mk _ = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

def toQuotH (F G : SubSystem S x Ω) :
    F.secs →ₗ[S] Cech.H (fun I => F.sub I ⧸ SubSystem.quotSub F G I) (SubSystem.quotRes F G) 0 :=
  toH0 (quotPi F G) (quotPi_res F G)

theorem ker_toQuotH (F G : SubSystem S x Ω) :
    LinearMap.ker (toQuotH F G) = G.secs.comap F.secs.subtype := by
  ext z
  rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
  unfold toQuotH
  rw [toH0_eq_zero_iff_components]
  constructor
  · intro h
    refine Submodule.mem_iInf _ |>.mpr fun I => ?_
    obtain ⟨i, hi⟩ := I.2.1
    have hsup : i ∈ support x := I.2.2 hi
    have h1 := (quotPi_eq_zero_iff F G _ z).mp (h (CechZerothCohomologySections.pt hsup))
    exact G.mono _ I (Finset.singleton_subset_iff.mpr hi) _ h1
  · intro h K
    exact (quotPi_eq_zero_iff F G _ z).mpr (CechZerothCohomologySections.mem_sub_of_mem_secs G h K.1)

theorem toQuotH_surjective (F G : SubSystem S x Ω)
    (hlift : ∀ σ : Chart x → Ω, (∀ I, σ I ∈ F.sub I) →
      (∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → σ I₁ - σ I₂ ∈ G.sub I₂) →
      ∃ t ∈ F.secs, ∀ I, t - σ I ∈ G.sub I) :
    Function.Surjective (toQuotH F G) := by
  refine toH0_surjective_of_lift _ _ fun s hs => ?_
  choose r hr using fun K : Cech.Idx (support x) 0 => Submodule.Quotient.mk_surjective _ (s K)

  let K0 : Chart x → Cech.Idx (support x) 0 := fun I => CechZerothCohomologySections.pt (I.2.2 (Finset.min'_mem I.1 I.2.1))
  have hK0 : ∀ I : Chart x, (K0 I).1.1 ⊆ I.1 := fun I =>
    Finset.singleton_subset_iff.mpr (Finset.min'_mem I.1 I.2.1)
  let σ : Chart x → Ω := fun I => (r (K0 I) : Ω)
  have hσ : ∀ I, σ I ∈ F.sub I := fun I => F.mono _ I (hK0 I) _ (r (K0 I)).2
  have hcompat : ∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → σ I₁ - σ I₂ ∈ G.sub I₂ := by
    intro I₁ I₂ h
    by_cases hab : I₁.1.min' I₁.2.1 = I₂.1.min' I₂.2.1
    · have hK : K0 I₁ = K0 I₂ := Subtype.ext (Subtype.ext (by
        change ({I₁.1.min' I₁.2.1} : Finset (Fin (N + 1))) = {I₂.1.min' I₂.2.1}
        rw [hab]))
      simp only [σ]
      rw [hK, sub_self]
      exact Submodule.zero_mem _
    · have hsub : ({I₁.1.min' I₁.2.1, I₂.1.min' I₂.2.1} : Finset (Fin (N + 1))) ⊆ support x := by
        rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨I₁.2.2 (Finset.min'_mem _ _), I₂.2.2 (Finset.min'_mem _ _)⟩
      let J : Cech.Idx (support x) 1 := ⟨⟨_, Finset.insert_nonempty _ _, hsub⟩, Finset.card_pair hab⟩
      have hJ : J.1.1 ⊆ I₂.1 := by
        rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨h (Finset.min'_mem _ _), Finset.min'_mem _ _⟩
      have hKa : (K0 I₁).1.1 ⊆ J.1.1 := Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)
      have hKb : (K0 I₂).1.1 ⊆ J.1.1 :=
        Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      have hne : (K0 I₁).1.1 ≠ (K0 I₂).1.1 := fun he => hab (Finset.singleton_inj.mp he)
      have e := cocycle_res_eq hs (K0 I₁) (K0 I₂) J hKa hKb hne
      rw [← hr (K0 I₁), ← hr (K0 I₂)] at e
      change (Submodule.Quotient.mk (F.res (K0 I₁).1 J.1 hKa (r (K0 I₁))) :
          F.sub J.1 ⧸ SubSystem.quotSub F G J.1) = Submodule.Quotient.mk (F.res (K0 I₂).1 J.1 hKb (r (K0 I₂))) at e
      rw [Submodule.Quotient.eq] at e
      exact G.mono J.1 I₂ hJ _ e
  obtain ⟨t, ht, hts⟩ := hlift σ hσ hcompat
  refine ⟨⟨t, ht⟩, fun K => ?_⟩
  rw [← hr K]
  change (Submodule.Quotient.mk (secsIncl F K.1 ⟨t, ht⟩) : F.sub K.1 ⧸ SubSystem.quotSub F G K.1) =
    Submodule.Quotient.mk (r K)
  rw [Submodule.Quotient.eq]
  have hK : K0 K.1 = K := by
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp K.2
    have hm : K.1.1.min' K.1.2.1 ∈ ({a} : Finset (Fin (N + 1))) := by
      rw [← ha]; exact Finset.min'_mem _ _
    refine Subtype.ext (Subtype.ext ?_)
    change ({K.1.1.min' K.1.2.1} : Finset (Fin (N + 1))) = K.1.1
    rw [Finset.mem_singleton.mp hm, ha]
  have h1 := hts K.1
  simp only [σ] at h1
  rw [hK] at h1
  exact h1

def quotEquiv (F G : SubSystem S x Ω)
    (hlift : ∀ σ : Chart x → Ω, (∀ I, σ I ∈ F.sub I) →
      (∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → σ I₁ - σ I₂ ∈ G.sub I₂) →
      ∃ t ∈ F.secs, ∀ I, t - σ I ∈ G.sub I) :
    (F.secs ⧸ G.secs.comap F.secs.subtype) ≃ₗ[S] SubSystem.quotH F G 0 :=
  (Submodule.quotEquivOfEq _ _ (ker_toQuotH F G).symm).trans
    (LinearMap.quotKerEquivOfSurjective (toQuotH F G) (toQuotH_surjective F G hlift))

end Quot

section Point

variable {S : Type u} [CommRing S] {K' : Type w} [Field K'] [Algebra S K'] {N : ℕ}

theorem restrLen_primeOf (y : Fin (N + 1) → K') {j : Fin (N + 1)} (hyj : y j ≠ 0)
    (F : SubSystem S y K') :
    restrLen (primeOf (S := S) y) F = ((Module.length S F.secs).toNat : ℤ) := by
  have hid : ∀ I : Chart y, idealMod (x := y) (primeOf (S := S) y) I = ⊥ := by
    intro I
    refine Submodule.span_eq_bot.mpr ?_
    rintro _ ⟨f, s, e, hf, _, hfe, _, rfl⟩
    rw [(mem_primeOf_of_isHomogeneous y hfe).mp hf, zero_div]
  have hbot : ∀ I : Chart y, (F.twist (idealSys y (primeOf (S := S) y))).sub I = ⊥ := by
    intro I
    refine Submodule.span_eq_bot.mpr ?_
    rintro _ ⟨q, hq, z, _, rfl⟩
    have hq' : q ∈ idealMod (x := y) (primeOf (S := S) y) I := hq
    rw [hid I, Submodule.mem_bot] at hq'
    rw [hq', zero_smul]
  have hsecs : (F.twist (idealSys y (primeOf (S := S) y))).secs = ⊥ := by
    refine eq_bot_iff.mpr fun z hz => ?_
    have h1 := (Submodule.mem_iInf _).mp hz (singleChart hyj)
    rw [Submodule.restrictScalars_mem, hbot] at h1
    exact h1
  unfold restrLen
  rw [hsecs, Submodule.comap_bot, Submodule.ker_subtype,
    (Submodule.quotEquivOfEqBot (⊥ : Submodule S F.secs) rfl).length_eq]

end Point

end CycleSplit.Curve.Restr

open CycleSplit.Curve.Restr in

theorem CycleSplit.Curve.Restr.proof (hSC : SurjectiveClosed.Statement.{u, w})
    (hRQ : PrimeFiltration.RestrictQuot.Statement.{u, w}) : CycleSplit.Curve.Restr.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x pp hpp hhom hle j hj hX K' _ _ ψ hker hxy Q Q' r hRD
  have hpy : primeOf (S := S) (fun i => ψ (ratio hj i)) = pp :=
    (PrimeFiltration.Point.proof S Ω N x pp hpp hhom hle j hj hX).2 K' ψ hker
  have hyj : ψ (ratio hj j) ≠ 0 := by
    have : ratio (S := S) hj j = 1 := Subtype.ext (div_self hj)
    rw [this, map_one]
    exact one_ne_zero
  have hy0 : (fun i => ψ (ratio hj i)) ≠ 0 := fun h0 => hyj (congrFun h0 j)
  obtain ⟨c₀, hc₀⟩ := hSC S Ω N x Q pp hhom
  filter_upwards [eventually_ge_atTop c₀.toNat] with c hc
  have hcc : c₀ ≤ (c : ℤ) := by omega
  obtain ⟨E1⟩ := hRQ S Ω N x pp hpp hhom hle j hj hX K' ψ hker hxy Q Q' r hRD c 0
  obtain ⟨E2⟩ := CechZerothCohomologySections.proof S K' N _ K'
    (Q'.toSubSystem.twist (twistSys S (fun l => ψ (ratio hj l)) c)) hy0
  have E0 := quotEquiv (Q.toSubSystem.twist (twistSys S x c))
    ((Q.toSubSystem.twist (twistSys S x c)).twist (idealSys x pp)) (hc₀ c hcc)
  conv_rhs => rw [← hpy]
  rw [restrLen_primeOf _ hyj]
  unfold restrLen
  rw [(E0.trans (E1.trans E2)).length_eq]

end

end GroundTheory.Heights₂.Heights.Kleiman
