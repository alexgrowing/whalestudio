import Formalism.LocalToGlobal.NormalizedHeckeFactors.ChiDefs

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace Formalism.L2.NC

def iotaC (D : D7) (i : D.nd.Loc) : D.nd.O i →+* ℂ :=
  ((D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i)).comp (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))

def complexEmbeddingRestrictedToSubfield (D : D7) : ↥D.LL0 →+* ℂ := D.what₂.embLL.comp D.LL0.val.toRingHom

structure NChiData (D : D7) where

  mu0 : ℕ → HC D.host.E

  etaT : HC D.host.E

  del : D.ntw.Tw → HC D.host.E

  psi : D.nd.Loc → HC D.host.E

  chiI : ∀ s, D.ntw.abelian₂ s → HC D.host.E

  embO : ∀ s, Bool → ↥D.LL0 →+* FractionRing (D.ntw.O s)

def NChiData.firstHeckeCharacter {D : D7} (K : NChiData D) (s : D.ntw.Tw) (j : ℕ) : HC D.host.E :=
  K.mu0 j * K.del s * (K.etaT)⁻¹

def NChiData.lamH {D : D7} (K : NChiData D) (s : D.ntw.Tw) (lam : D.ntw.abelian₂ s) : HC D.host.E :=
  K.mu0 (D.ntw.jL s lam) * K.del s * (K.chiI s lam)⁻¹

def NChiData.chiH {D : D7} (K : NChiData D) (a : D.nd.Loc) : HC D.host.E :=
  K.firstHeckeCharacter (D.ntw.twOf a) (D.nd.j a) * K.psi a

structure NormalizedCharacterCompatibility (D : D7) (K : NChiData D) : Prop where

  psi : ∀ a, ReadC D.nd.plOm.1 (D.ntw.psiL a) (iotaC D a) (K.psi a) 0

  del_fix : ∀ s s', D.ntw.pD s = D.ntw.pD s' → K.del s = K.del s'

  delta : ∀ s, Read D.nd.plOm.1 (D.ntw.delta s) (algebraMap (D.ntw.O0 s) (FractionRing (D.ntw.O0 s))) (D.ntw.emb0 s)
    (complexEmbeddingRestrictedToSubfield D) (K.del s) 0

  chi1 : ∀ s j (b : Bool), 1 ≤ j → j ≤ D.R.m → Read D.nd.plOm.1 (D.ntw.chi1 s j b) (algebraMap (D.ntw.O0 s) (FractionRing (D.ntw.O0 s)))
    (if b then D.ntw.emb0 s else D.ntw.emb0b s) (complexEmbeddingRestrictedToSubfield D) (K.firstHeckeCharacter s j) (-(D.R.r : ℤ))

  ringSpec_sidedEmbedding_fixedField : ∀ s (b : Bool) (x : ↥D.LL0) (y : D.ntw.O0 s),
    algebraMap (D.ntw.O0 s) (FractionRing (D.ntw.O0 s)) y = (if b then D.ntw.emb0 s else D.ntw.emb0b s) x →
    K.embO s b x = algebraMap (D.ntw.O s) (FractionRing (D.ntw.O s)) (algebraMap (D.ntw.O0 s) (D.ntw.O s) y)

  etaT_unr : ∀ P, K.etaT.Unr P

  etaT_inf : ∀ g : D.R.Psi, K.etaT.IsUnitArg (D.host.emb (g : D.R.GG))

  lamG : ∀ s lam, Read D.nd.plOm.1 (D.ntw.lamG s lam) (algebraMap (D.ntw.O s) (FractionRing (D.ntw.O s)))
    (K.embO s (D.ntw.sideL s lam)) (complexEmbeddingRestrictedToSubfield D) (K.lamH s lam) 0

theorem chi_read {D : D7} {K : NChiData D} (T : NormalizedCharacterCompatibility D K) (a : D.nd.Loc) :
    ReadC D.nd.plOm.1 (D.nd.chi a 1) (iotaC D a) (K.chiH a) (-(D.R.r : ℤ)) := by
  classical
  obtain ⟨B1, h1⟩ := T.chi1 (D.ntw.twOf a) (D.nd.j a) (D.ntw.twSide a) (D.nd.j_range a).1 (D.nd.j_range a).2
  obtain ⟨B2, h2⟩ := T.psi a
  refine ⟨B1 ∪ B2, fun P hP => ?_⟩
  obtain ⟨α1, hα1, x1, hx1, hσ1⟩ := h1 P (fun h => hP (Finset.mem_union_left _ h))
  obtain ⟨α2, hα2, x2, hx2, hσ2⟩ := h2 P (fun h => hP (Finset.mem_union_right _ h))
  refine ⟨α1 * α2, hα1.mul hα2, (α1 * α2)⁻¹ * (Real.sqrt (normV P) : ℂ) ^ (-(D.R.r : ℤ)), rfl, fun σ hσ => ?_⟩
  have e1 := hσ1 σ hσ
  have e2 := hσ2 σ hσ
  simp only [RingHom.id_apply] at hx2 e2 ⊢
  have tw := D.ntw.twO_emb a x1 _ e1
  have hc : (D.nd.chi a 1 σ : D.nd.O a) =
      D.ntw.twist₂ a (D.ntw.chi1 (D.ntw.twOf a) (D.nd.j a) (D.ntw.twSide a) σ : D.ntw.O0 (D.ntw.twOf a)) *
        (D.ntw.psiL a σ : D.nd.O a) := by
    rw [D.ntw.chi_tw a]
    rfl
  rw [hc, map_mul, e2, hx2]
  have h3 : iotaC D a (D.ntw.twist₂ a (D.ntw.chi1 (D.ntw.twOf a) (D.nd.j a) (D.ntw.twSide a) σ :
      D.ntw.O0 (D.ntw.twOf a))) = complexEmbeddingRestrictedToSubfield D x1 := by
    simp only [iotaC, RingHom.comp_apply, complexEmbeddingRestrictedToSubfield]
    rw [← tw]
    exact D.naut.iota_LL a (x1 : D.what₂.LL)
  rw [h3, hx1, zpow_zero, mul_one, mul_inv]
  ring

section rcg

variable (D : D7)

theorem art_ker (s : D.ntw.Tw) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (hQ : ∀ v ∈ Q, v ∉ placesOver D.host.E (D.ntw.l s)) :
    (D.ntw.art s Q).ker = rcgKer D.ntw.cc (D.ntw.l s) (Q : Set (HeightOneSpectrum (𝓞 D.host.E))) := by
  ext g
  constructor
  · intro hg
    refine mem_rcgKer.2 fun A _ φ hφ => ?_
    obtain ⟨hfin, hl, hop, han, hun⟩ := hφ
    have := hfin
    obtain ⟨f, hf⟩ := D.ntw.art_univ s Q hQ A hl φ hop han (fun v hv A' hA σ hσ => hun v hv A' hA σ hσ)
    rw [← hf, MonoidHom.comp_apply, (MonoidHom.mem_ker).1 hg, map_one]
  · intro hg
    exact (mem_rcgKer.1 hg) _ (D.ntw.art s Q) ⟨inferInstance, D.ntw.RCG_l s Q, D.ntw.art_cont s Q, D.ntw.art_anti s Q,
      fun v hv A hA σ hσ => D.ntw.art_unr s Q v hv A hA σ hσ⟩

def rcgEquiv (s : D.ntw.Tw) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (hQ : ∀ v ∈ Q, v ∉ placesOver D.host.E (D.ntw.l s)) :
    D.ntw.RCG s Q ≃* RCGGal D.ntw.cc (D.ntw.l s) (Q : Set (HeightOneSpectrum (𝓞 D.host.E))) :=
  (QuotientGroup.quotientKerEquivOfSurjective _ (D.ntw.art_surj s Q)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (art_ker D s Q hQ))

theorem rcgEquiv_art (s : D.ntw.Tw) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (hQ : ∀ v ∈ Q, v ∉ placesOver D.host.E (D.ntw.l s)) (g : G D.host.E D.nd.Om) :
    rcgEquiv D s Q hQ (D.ntw.art s Q g) = artGal D.ntw.cc (D.ntw.l s) (Q : Set (HeightOneSpectrum (𝓞 D.host.E))) g := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective _ (D.ntw.art_surj s Q)).symm (D.ntw.art s Q g) =
      (QuotientGroup.mk g : G D.host.E D.nd.Om ⧸ (D.ntw.art s Q).ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [rcgEquiv, MulEquiv.trans_apply, h1]
  rfl

theorem res_eq (s : D.ntw.Tw) (Q Q' : Finset (HeightOneSpectrum (𝓞 D.host.E))) (h : Q' ⊆ Q)
    (f : D.ntw.RCG s Q →* D.ntw.RCG s Q') (hf : f.comp (D.ntw.art s Q) = D.ntw.art s Q') :
    f = D.ntw.res s Q Q' h := by
  apply MonoidHom.ext
  intro x
  obtain ⟨g, rfl⟩ := D.ntw.art_surj s Q x
  have h1 := congrArg (fun φ => φ g) hf
  simp only [MonoidHom.comp_apply] at h1
  first
  | (have h2 := congrArg (fun φ => φ g) (D.ntw.res_art s Q Q' h)
     simp only [MonoidHom.comp_apply] at h2
     rw [h1, h2])
  | rw [h1, D.ntw.res_art s Q Q' h g]

theorem psiL_factor (a : D.nd.Loc) :
    ∃ f : D.ntw.RCG (D.ntw.twOf a) (D.nd.Q a) →* (D.nd.O a)ˣ,
      f.comp (D.ntw.art (D.ntw.twOf a) (D.nd.Q a)) = D.ntw.psiL a := by
  have hfin : Finite (D.ntw.psiL a).range := by
    have : Finite (G D.host.E D.nd.Om ⧸ (D.ntw.psiL a).ker) :=
      Subgroup.quotient_finite_of_isOpen _ (D.ntw.psiL_open a)
    exact Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange (D.ntw.psiL a)).toEquiv
  have hQ : ∀ v ∈ D.nd.Q a, v ∉ placesOver D.host.E (D.ntw.l (D.ntw.twOf a)) := by
    intro v hv
    rw [D.ntw.twOf_l]
    exact D.nd.SQ_l a v (Or.inr hv)
  have hl : ∀ x : (D.ntw.psiL a).range, ∃ n : ℕ, x ^ (D.ntw.l (D.ntw.twOf a) ^ n) = 1 := by
    rintro ⟨_, g, rfl⟩
    obtain ⟨n, hn⟩ := D.ntw.psiL_ord a g
    refine ⟨n, Subtype.ext ?_⟩
    rw [D.ntw.twOf_l]
    simpa using hn
  have hop : IsOpen ((D.ntw.psiL a).rangeRestrict.ker : Set (G D.host.E D.nd.Om)) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact D.ntw.psiL_open a
  have han : AntiHom D.ntw.cc (D.ntw.psiL a).rangeRestrict := fun g g' h =>
    Subtype.ext (by simpa using D.ntw.psiL_anti a g g' h)
  have hun : ∀ v, v ∉ D.nd.Q a → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v →
      ∀ σ ∈ Ine (F := D.host.E) A, (D.ntw.psiL a).rangeRestrict σ = 1 := by
    intro v hv A hA σ hσ
    apply Subtype.ext
    simp only [MonoidHom.coe_rangeRestrict, OneMemClass.coe_one]
    by_contra hne
    exact hv ((D.ntw.psiL_ram a v A hA).1 ⟨σ, hσ, hne⟩)
  obtain ⟨f, hf⟩ := D.ntw.art_univ (D.ntw.twOf a) (D.nd.Q a) hQ (D.ntw.psiL a).range hl _ hop han hun
  refine ⟨(D.ntw.psiL a).range.subtype.comp f, ?_⟩
  rw [MonoidHom.comp_assoc, hf]
  rfl

end rcg

theorem chi_ram_Q_of_tw (D : D7) (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ D.nd.Q i) :
    ∃ g ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), D.nd.chi i 1 g ≠ 1 := by
  have hS : v ∉ D.nd.S i := fun h => Finset.disjoint_left.1 (D.nd.SQ_disj i) h hv
  have hl : v ∉ placesOver D.host.E (D.nd.l i) := D.nd.SQ_l i v (Or.inr hv)
  have hg : ∀ k, v ∉ placesOver D.host.E (D.host.g k) := by
    intro k hk
    apply hS
    rw [D.nd.S_def i v]
    refine ⟨?_, hl⟩
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk)
  have hpd : v ∉ D.ntw.pD (D.ntw.twOf i) := by
    intro hp
    have h' : v ∈ ((D.ntw.pD (D.ntw.twOf i) : Finset _) : Set (HeightOneSpectrum (𝓞 D.host.E))) := hp
    rw [D.ntw.pD_eq, D.ntw.twOf_l] at h'
    exact hS ((D.nd.S_def i v).2 ⟨Or.inr (Or.inr h'), hl⟩)
  have hl' : v ∉ placesOver D.host.E (D.ntw.l (D.ntw.twOf i)) := by
    rw [D.ntw.twOf_l]
    exact hl
  obtain ⟨σ, hσ, hψ⟩ := (D.ntw.psiL_ram i v (D.nd.plOm.1 v) (D.nd.plOm.2 v)).2 hv
  refine ⟨σ, hσ, ?_⟩
  have h1 := D.ntw.twistCharacterFamily_unramified (D.ntw.twOf i) (D.nd.j i) (D.ntw.twSide i) v hl' hg hpd (D.nd.plOm.1 v) (D.nd.plOm.2 v) σ hσ
  rw [D.ntw.chi_tw i, MonoidHom.mul_apply, MonoidHom.comp_apply, h1, map_one, one_mul]
  exact hψ

theorem Xv_read {D : D7} {K : NChiData D} (T : NormalizedCharacterCompatibility D K) (s : D.ntw.Tw) (lam : D.ntw.abelian₂ s) :
    ∃ B : Finset (HeightOneSpectrum (𝓞 D.host.E)), ∀ P ∉ B, ∃ α : ℂ, (K.lamH s lam).At P α ∧ ∃ x : ↥D.LL0,
      complexEmbeddingRestrictedToSubfield D x = α⁻¹ ∧
      ∀ σ : G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ →
        algebraMap (D.ntw.O s) (FractionRing (D.ntw.O s)) (D.ntw.Xv s lam P) = K.embO s (D.ntw.sideL s lam) x := by
  classical
  obtain ⟨B, hB⟩ := T.lamG s lam
  refine ⟨B ∪ D.ntw.S0 s, fun P hP => ?_⟩
  obtain ⟨α, hα, x, hx, hσ⟩ := hB P (fun h => hP (Finset.mem_union_left _ h))
  refine ⟨α, hα, x, by rw [hx, zpow_zero, mul_one], fun σ hσ' => ?_⟩
  rw [D.ntw.Xv_def s lam P (fun h => hP (Finset.mem_union_right _ h)) σ hσ']
  exact hσ σ hσ'

theorem units_zpow_map {O : Type} [CommRing O] (f : O →+* ℂ) (u : Oˣ) (n : ℤ) :
    f ((u ^ n : Oˣ) : O) = (f (u : O)) ^ n := by
  have h2 := congrArg (fun v : ℂˣ => (v : ℂ)) (map_zpow (Units.map f.toMonoidHom) u n)
  simp only [Units.coe_map, Units.val_zpow_eq_zpow_val, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at h2
  exact h2

theorem chi_c_read {D : D7} {K : NChiData D} (T : NormalizedCharacterCompatibility D K) (a : D.nd.Loc) (c : ℕ) (h1 : 1 ≤ c) (h2 : c ≤ D.R.t) :
    ReadC D.nd.plOm.1 (D.nd.chi a c) (iotaC D a) (K.chiH a) (-(D.R.r : ℤ) - 2 * ((c : ℤ) - 1)) := by
  classical
  have : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  have : CharZero D.nd.Om := charZero_of_injective_algebraMap (algebraMap D.host.E D.nd.Om).injective
  have hcyc : CycFrob D.nd.plOm.1 (D.nd.l a) := cycFrob_holds D.nd.plOm.1 D.nd.plOm.2 (D.nd.l a)
  obtain ⟨B, hB⟩ := chi_read T a
  have hfin := finite_placesOver (E := D.host.E) (D.nd.l a)
  refine ⟨B ∪ hfin.toFinset, fun P hP => ?_⟩
  obtain ⟨α, hα, x, hx, hσ⟩ := hB P (fun h => hP (Finset.mem_union_left _ h))
  have hl : ((D.nd.l a : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := fun h =>
    hP (Finset.mem_union_right _ (hfin.mem_toFinset.2 h))
  refine ⟨α, hα, α⁻¹ * (Real.sqrt (normV P) : ℂ) ^ (-(D.R.r : ℤ) - 2 * ((c : ℤ) - 1)), rfl, fun σ hσ' => ?_⟩
  simp only [RingHom.id_apply] at hx hσ ⊢
  have e := hσ σ hσ'
  rw [hx] at e
  have hq := hcyc P hl σ hσ'
  have hcy : iotaC D a ((((Units.map (algebraMap ℤ_[D.nd.l a] (D.nd.O a)).toMonoidHom).comp
      (cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l a))) σ : (D.nd.O a)ˣ) : D.nd.O a) = (normV P : ℂ) := by
    simp only [MonoidHom.comp_apply, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, hq, map_natCast]
  have hs : ((Real.sqrt (normV P) : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt (normV P) := Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero (normV_ne_zero P)))
    exact_mod_cast this.ne'
  have hsq : (normV P : ℂ) = ((Real.sqrt (normV P) : ℝ) : ℂ) ^ (2 : ℤ) := by
    rw [zpow_two, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    simp
  rw [D.nd.chi_def a c h1 h2, MonoidHom.mul_apply, Units.val_mul, map_mul, e, MonoidHom.zpow_apply,
    units_zpow_map, hcy, hsq, ← zpow_mul, mul_assoc, ← zpow_add₀ hs]
  congr 2
  ring

theorem rcgOpen_of_record (D : D7) (s : D.ntw.Tw) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (hQ : ∀ v ∈ Q, v ∉ placesOver D.host.E (D.ntw.l s)) :
    RcgOpen D.ntw.cc (D.ntw.l s) (Q : Set (HeightOneSpectrum (𝓞 D.host.E))) := by
  intro _ _ _ _
  rw [← art_ker D s Q hQ]
  exact D.ntw.art_cont s Q

theorem rcgGal_second (D : D7) (s : D.ntw.Tw) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (hQ : ∀ v ∈ Q, v ∉ placesOver D.host.E (D.ntw.l s)) :
    Finite (RCGGal D.ntw.cc (D.ntw.l s) (Q : Set (HeightOneSpectrum (𝓞 D.host.E)))) ∧
      (∀ x : RCGGal D.ntw.cc (D.ntw.l s) (Q : Set (HeightOneSpectrum (𝓞 D.host.E))), ∃ n : ℕ, x ^ (D.ntw.l s ^ n) = 1) ∧
      IsOpen ((artGal D.ntw.cc (D.ntw.l s) (Q : Set (HeightOneSpectrum (𝓞 D.host.E)))).ker : Set (G D.host.E D.nd.Om)) ∧
      AntiHom D.ntw.cc (artGal D.ntw.cc (D.ntw.l s) (Q : Set (HeightOneSpectrum (𝓞 D.host.E)))) ∧
      UnrOut (artGal D.ntw.cc (D.ntw.l s) (Q : Set (HeightOneSpectrum (𝓞 D.host.E)))) (Q : Set (HeightOneSpectrum (𝓞 D.host.E))) ∧
      Function.Surjective (artGal D.ntw.cc (D.ntw.l s) (Q : Set (HeightOneSpectrum (𝓞 D.host.E)))) :=
  have hO : IsOpen ((rcgKer D.ntw.cc (D.ntw.l s) (Q : Set (HeightOneSpectrum (𝓞 D.host.E))) : Subgroup _) :
      Set (G D.host.E D.nd.Om)) := by
    rw [← art_ker D s Q hQ]
    exact D.ntw.art_cont s Q
  ⟨rcgGal_finite _ _ _ hO, rcgGal_lpow _ _ _ hO, by rw [artGal_ker]; exact hO, artGal_anti _ _ _, artGal_unr _ _ _,
    artGal_surj _ _ _⟩

theorem frob_exists (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) :
    ∃ σ : G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ :=
  exists_isFrob (D.nd.plOm.2 P)

end Formalism.L2.NC
