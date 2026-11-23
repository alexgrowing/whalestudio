import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.NonEllFlag
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyBlockAndInvariantUnderStabilizerNilradic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwCentPreservesFlag
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalIntertwining

open Polynomial Matrix PositivityTheory.Rg.BcB

noncomputable section

namespace GlobalTheory.CompanionTheory.PairParam

section Comb

variable {A : Type} [Finite A]

theorem exists_signs (ι : A → A) (hι : ∀ a, ι (ι a) = a) :
    ∃ (m : ℕ) (T : (Fin m → SignType) → Set A), (∀ e, ∀ a ∈ T e, ι a ∉ T e) ∧
      (∀ I : Set A, (∀ a ∈ I, ι a ∉ I) → ∃! e, T e = I) ∧ T 0 = ∅ ∧
      (∀ e e', T (sMeet e e') = T e ∩ T e') ∧ (∀ e e', SLe e e' → T e ⊆ T e') := by
  classical
  obtain ⟨k, ⟨q⟩⟩ := Finite.exists_equiv_fin A
  letI : Fintype A := Fintype.ofEquiv _ q.symm
  letI : LinearOrder A := LinearOrder.lift' q q.injective
  let R : Finset A := Finset.univ.filter fun a => a < ι a
  let r : Fin R.card → A := fun j => (R.equivFin.symm j : A)
  have hr : ∀ j, r j < ι (r j) := fun j => (Finset.mem_filter.1 (R.equivFin.symm j).2).2
  have hinj : Function.Injective r := fun i j h => R.equivFin.symm.injective (Subtype.ext h)
  have hsurj : ∀ a, a < ι a → ∃ j, r j = a := fun a ha =>
    ⟨R.equivFin ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩⟩, by simp [r]⟩
  have hne : ∀ i j, r i ≠ ι (r j) := fun i j h => by
    have h1 : ι (r i) = r j := by rw [h, hι]
    have h2 := hr i
    have h3 := hr j
    rw [h1] at h2
    rw [← h] at h3
    exact lt_asymm h2 h3
  let T : (Fin R.card → SignType) → Set A := fun e =>
    {a | ∃ j, (a = r j ∧ e j = 1) ∨ (a = ι (r j) ∧ e j = -1)}
  have hpos : ∀ e j, r j ∈ T e ↔ e j = 1 := fun e j => by
    constructor
    · rintro ⟨i, ⟨h, hi⟩ | ⟨h, _⟩⟩
      · rwa [hinj h]
      · exact absurd h (hne _ _)
    · exact fun h => ⟨j, Or.inl ⟨rfl, h⟩⟩
  have hneg : ∀ e j, ι (r j) ∈ T e ↔ e j = -1 := fun e j => by
    constructor
    · rintro ⟨i, ⟨h, _⟩ | ⟨h, hi⟩⟩
      · exact absurd h.symm (hne _ _)
      · have : r j = r i := by simpa [hι] using congrArg ι h
        rwa [hinj this]
    · exact fun h => ⟨j, Or.inr ⟨rfl, h⟩⟩
  have hext : ∀ e e', T e = T e' → e = e' := fun e e' h => by
    funext j
    have h1 := hpos e j
    have h2 := hneg e j
    rw [h] at h1 h2
    rw [hpos e' j] at h1
    rw [hneg e' j] at h2
    cases he : e j <;> cases he' : e' j <;> simp_all
  refine ⟨R.card, T, ?_, ?_, ?_, ?_, ?_⟩
  · rintro e a ⟨j, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩ hc
    · have := (hneg e j).1 hc
      rw [h] at this
      exact absurd this (by decide)
    · rw [hι] at hc
      have := (hpos e j).1 hc
      rw [h] at this
      exact absurd this (by decide)
  · intro I hI
    let e : Fin R.card → SignType := fun j => if r j ∈ I then 1 else if ι (r j) ∈ I then -1 else 0
    have he : T e = I := by
      ext a
      constructor
      · rintro ⟨j, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩
        · by_contra hc
          simp only [e, hc, if_false] at h
          split_ifs at h <;> exact absurd h (by decide)
        · by_contra hc
          simp only [e, hc, if_false] at h
          split_ifs at h <;> exact absurd h (by decide)
      · intro ha
        have hna := hI a ha
        rcases lt_trichotomy a (ι a) with h | h | h
        · obtain ⟨j, rfl⟩ := hsurj a h
          exact ⟨j, Or.inl ⟨rfl, by simp [e, ha]⟩⟩
        · rw [← h] at hna
          exact absurd ha hna
        · obtain ⟨j, hj⟩ := hsurj (ι a) (by rwa [hι])
          refine ⟨j, Or.inr ⟨by rw [hj, hι], ?_⟩⟩
          have h2 : ι (r j) ∈ I := by rwa [hj, hι]
          have h3 : r j ∉ I := by rwa [hj]
          simp [e, h2, h3]
    exact ⟨e, he, fun e' h => hext _ _ (h.trans he.symm)⟩
  · ext a
    simp [T]
  · intro e e'
    ext a
    constructor
    · rintro ⟨j, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩
      · have h1 : e j = e' j ∧ e j = 1 := by
          by_cases hc : e j = e' j
          · simpa [sMeet, hc] using h
          · simp [sMeet, hc] at h
        exact ⟨(hpos _ _).2 h1.2, (hpos _ _).2 (h1.1 ▸ h1.2)⟩
      · have h1 : e j = e' j ∧ e j = -1 := by
          by_cases hc : e j = e' j
          · simpa [sMeet, hc] using h
          · simp [sMeet, hc] at h
        exact ⟨(hneg _ _).2 h1.2, (hneg _ _).2 (h1.1 ▸ h1.2)⟩
    · rintro ⟨⟨j, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩, h2⟩
      · have h3 := (hpos _ _).1 h2
        exact ⟨j, Or.inl ⟨rfl, by simp [sMeet, h, h3]⟩⟩
      · have h3 := (hneg _ _).1 h2
        exact ⟨j, Or.inr ⟨rfl, by simp [sMeet, h, h3]⟩⟩
  · intro e e' h a
    rintro ⟨j, ⟨rfl, h1⟩ | ⟨rfl, h1⟩⟩
    · exact ⟨j, Or.inl ⟨rfl, by rw [h j (by rw [h1]; decide), h1]⟩⟩
    · exact ⟨j, Or.inr ⟨rfl, by rw [h j (by rw [h1]; decide), h1]⟩⟩

end Comb

theorem exists_invol {A : Type} (c : Set A → Set A) (hanti : Antitone c) (hinv : ∀ I, c (c I) = I) :
    ∃ ι : A → A, (∀ a, ι (ι a) = a) ∧ ∀ I, c I = (ι '' I)ᶜ := by
  classical

  let cd : Set A ≃o (Set A)ᵒᵈ :=
    { toFun := fun I => OrderDual.toDual (c I)
      invFun := fun I => c (OrderDual.ofDual I)
      left_inv := hinv
      right_inv := fun I => by simp [hinv]
      map_rel_iff' := by
        intro I J
        constructor
        · intro h
          have := hanti (show c J ≤ c I from h)
          rwa [hinv, hinv] at this
        · intro h
          exact hanti h }
  have hcompl : ∀ I, c Iᶜ = (c I)ᶜ := fun I => by
    have h := cd.isCompl (isCompl_compl (x := I))
    have h2 : IsCompl (c I) (c Iᶜ) := h.ofDual
    exact h2.compl_eq.symm
  let ψ : Set A ≃o Set A :=
    { toFun := fun I => (c I)ᶜ
      invFun := fun I => (c I)ᶜ
      left_inv := fun I => by simp [← hcompl, hinv]
      right_inv := fun I => by simp [← hcompl, hinv]
      map_rel_iff' := by
        intro I J
        constructor
        · intro h
          have h1 : c J ≤ c I := compl_le_compl_iff_le.1 h
          have := hanti h1
          rwa [hinv, hinv] at this
        · intro h
          exact compl_le_compl (hanti h) }
  have hatom : ∀ a, ∃ b, ψ {a} = {b} := fun a =>
    Set.isAtom_iff.1 ((ψ.isAtom_iff _).2 (Set.isAtom_singleton a))
  choose ι hι using hatom
  have hψψ : ∀ I, ψ (ψ I) = I := fun I => ψ.left_inv I
  have hsub : ∀ I, ∀ a ∈ I, ι a ∈ ψ I := fun I a ha => by
    have h1 : ψ {a} ≤ ψ I := ψ.monotone (Set.singleton_subset_iff.2 ha)
    rw [hι] at h1
    exact h1 rfl
  have hιι : ∀ a, ι (ι a) = a := fun a => by
    have h1 := hψψ {a}
    rw [hι, hι] at h1
    exact Set.singleton_injective h1
  refine ⟨ι, hιι, fun I => ?_⟩
  have h2 : ψ I = ι '' I := by
    ext b
    constructor
    · intro hb
      have := hsub _ _ hb
      rw [hψψ] at this
      exact ⟨_, this, hιι b⟩
    · rintro ⟨a, ha, rfl⟩
      exact hsub _ _ ha
  rw [← h2]
  exact (compl_compl _).symm

section Lin

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem aeval_intertwine {M N : Type} [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] (φ : M →ₗ[K] N)
    (f : Module.End K M) (f' : Module.End K N) (h : ∀ x, φ (f x) = f' (φ x)) (p : K[X]) (x : M) :
    φ (aeval f p x) = aeval f' p (φ x) :=
  _root_.UpperTheory.Reformulated.B.AevalIntertwining.aeval_intertwine φ f f' h p x

theorem aeval_restrict_coe (f : Module.End K V) (W : Submodule K V) (hW : ∀ x ∈ W, f x ∈ W) (p : K[X]) (w : W) :
    ((aeval (f.restrict hW : Module.End K W) p) w : V) = aeval f p (w : V) :=
  (aeval_intertwine W.subtype (f.restrict hW) f (fun _ => rfl) p w)

theorem aeval_mem (f : Module.End K V) (W : Submodule K V) (hW : ∀ x ∈ W, f x ∈ W) (p : K[X]) {w : V} (hw : w ∈ W) :
    aeval f p w ∈ W := by
  have := aeval_restrict_coe f W hW p ⟨w, hw⟩
  rw [← show _ = aeval f p w from this]
  exact Subtype.property _

theorem aeval_mapQ (f : Module.End K V) (W : Submodule K V) (hW : ∀ x ∈ W, f x ∈ W) (p : K[X]) (v : V) :
    aeval (W.mapQ W f (fun x hx => hW x hx) : Module.End K (V ⧸ W)) p (W.mkQ v) = W.mkQ (aeval f p v) :=
  (aeval_intertwine W.mkQ f (W.mapQ W f (fun x hx => hW x hx)) (fun _ => rfl) p v).symm

theorem invariant_eq_ker [FiniteDimensional K V] (f : Module.End K V) (hs : Squarefree f.charpoly) (W : Submodule K V)
    (hW : ∀ x ∈ W, f x ∈ W) : ∃ a b : K[X], a * b = f.charpoly ∧ W = LinearMap.ker (aeval f a) := by
  have hab := GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ W f hW
  set a := LinearMap.charpoly (f.restrict hW) with ha
  set b := LinearMap.charpoly (W.mapQ W f (fun x hx => hW x hx)) with hb
  refine ⟨a, b, hab.symm, le_antisymm ?_ ?_⟩
  · intro w hw
    have h1 := aeval_restrict_coe f W hW a ⟨w, hw⟩
    rw [ha, LinearMap.aeval_self_charpoly] at h1
    rw [LinearMap.mem_ker, ← show _ = aeval f _ w from h1]
    rfl
  · intro v hv
    rw [hab] at hs
    have hco : IsCoprime a b := (squarefree_mul_iff.1 hs).1.isCoprime
    obtain ⟨u, w, huw⟩ := hco
    have hbv : aeval f b v ∈ W := by
      have h1 := aeval_mapQ f W hW b v
      rw [hb, LinearMap.aeval_self_charpoly] at h1
      exact (Submodule.Quotient.mk_eq_zero W).1 h1.symm
    have h2 : v = aeval f w (aeval f b v) := by
      have h3 := congrArg (fun p => aeval f p v) huw
      simp only [map_add, map_mul, map_one, LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply] at h3
      rw [LinearMap.mem_ker.1 hv, map_zero, zero_add] at h3
      exact h3.symm
    rw [h2]
    exact aeval_mem f W hW w hbv

theorem ker_le_of_dvd (f : Module.End K V) {P p : K[X]} (h : P ∣ p) :
    LinearMap.ker (aeval f P) ≤ LinearMap.ker (aeval f p) := by
  obtain ⟨c, rfl⟩ := h
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  rw [mul_comm, map_mul, Module.End.mul_apply, hx, map_zero]

theorem exists_atoms [FiniteDimensional K V] (f : Module.End K V) (hs : Squarefree f.charpoly) :
    ∃ (A : Type) (_ : Finite A) (L : A → Submodule K V), iSupIndep L ∧ (∀ i, L i ≠ ⊥) ∧
      (∀ i, ∀ x ∈ L i, f x ∈ L i) ∧
      ∀ W : Submodule K V, (∀ x ∈ W, f x ∈ W) → ∃ I : Set A, W = ⨆ i ∈ I, L i := by
  classical
  have hm : f.charpoly.Monic := LinearMap.charpoly_monic f
  let F := (UniqueFactorizationMonoid.normalizedFactors f.charpoly).toFinset
  let Lk : K[X] → Submodule K V := fun P => LinearMap.ker (aeval f P)
  have hnd := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hm.ne_zero).1 hs
  have hprod : ∏ P ∈ F, P = f.charpoly := by
    have h1 : F.val = UniqueFactorizationMonoid.normalizedFactors f.charpoly := by
      simp only [F, Multiset.toFinset_val, hnd.dedup]
    rw [Finset.prod, h1, Multiset.map_id', UniqueFactorizationMonoid.prod_normalizedFactors_eq hm.ne_zero,
      hm.normalize_eq_self]
  have hirr : ∀ P ∈ F, Irreducible P := fun P hP =>
    UniqueFactorizationMonoid.irreducible_of_normalized_factor P (Multiset.mem_toFinset.1 hP)
  have hnorm : ∀ P ∈ F, normalize P = P := fun P hP =>
    UniqueFactorizationMonoid.normalize_normalized_factor P (Multiset.mem_toFinset.1 hP)
  have hcop : ∀ P ∈ F, ∀ Q ∈ F, P ≠ Q → IsCoprime P Q := fun P hP Q hQ hne => by
    refine ((hirr P hP).coprime_iff_not_dvd).2 fun hd => hne ?_
    exact dvd_antisymm_of_normalize_eq (hnorm P hP) (hnorm Q hQ) hd ((hirr P hP).dvd_symm (hirr Q hQ) hd)
  have hker : ∀ s : Finset K[X], s ⊆ F → LinearMap.ker (aeval f (∏ P ∈ s, P)) = ⨆ P ∈ s, Lk P := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.prod_empty, map_one, Finset.notMem_empty, iSup_false, iSup_bot]
      exact LinearMap.ker_id
    | insert a s ha ih =>
      intro hsF
      have hs' : s ⊆ F := (Finset.subset_insert a s).trans hsF
      have haF : a ∈ F := hsF (Finset.mem_insert_self a s)
      rw [Finset.prod_insert ha, ← sup_ker_aeval_eq_ker_aeval_mul_of_coprime, ih hs', Finset.iSup_insert]
      exact IsCoprime.prod_right fun b hb => hcop a haF b (hs' hb) fun h => ha (h ▸ hb)
  have htop : ⨆ P ∈ F, Lk P = ⊤ := by
    rw [← hker F subset_rfl, hprod, LinearMap.aeval_self_charpoly, LinearMap.ker_zero]
  let A := {P : K[X] // P ∈ F ∧ Lk P ≠ ⊥}
  haveI : Finite A := Finite.of_injective (fun a : A => (⟨a.1, a.2.1⟩ : F))
    (fun a b h => Subtype.ext (congrArg (fun z : {x // x ∈ F} => z.1) h))
  let L : A → Submodule K V := fun a => Lk a.1
  refine ⟨A, inferInstance, L, ?_, fun a => a.2.2, fun a x hx => ?_, fun W hW => ?_⟩
  · intro a
    have hle : ⨆ j, ⨆ (_ : j ≠ a), L j ≤ LinearMap.ker (aeval f (∏ P ∈ F.erase a.1, P)) := by
      rw [hker _ (Finset.erase_subset _ _)]
      refine iSup₂_le fun j hj => ?_
      exact le_iSup₂_of_le j.1 (Finset.mem_erase.2 ⟨fun h => hj (Subtype.ext h), j.2.1⟩) le_rfl
    refine Disjoint.mono_right hle (disjoint_ker_aeval_of_isCoprime f ?_)
    exact IsCoprime.prod_right fun Q hQ =>
      hcop _ a.2.1 _ (Finset.mem_of_mem_erase hQ) (Finset.ne_of_mem_erase hQ).symm
  · have h1 : aeval f a.1 (f x) = f (aeval f a.1 x) := (aeval_intertwine f f f (fun _ => rfl) a.1 x).symm
    have h2 : aeval f a.1 x = 0 := hx
    show aeval f a.1 (f x) = 0
    rw [h1, h2, map_zero]
  · obtain ⟨p, q, hpq, hWe⟩ := invariant_eq_ker f hs W hW
    refine ⟨{a | a.1 ∣ p}, ?_⟩
    have h1 : ⨆ i ∈ {a : A | a.1 ∣ p}, L i ≤ W := by
      rw [hWe]
      exact iSup₂_le fun i hi => ker_le_of_dvd f hi
    have h2 : (⊤ : Submodule K V) ≤ (⨆ i ∈ {a : A | a.1 ∣ p}, L i) ⊔ ⨆ P ∈ F.filter (fun P => ¬ P ∣ p), Lk P := by
      rw [← htop]
      refine iSup₂_le fun P hP => ?_
      by_cases hd : P ∣ p
      · by_cases hb : Lk P = ⊥
        · rw [hb]; exact bot_le
        · exact le_sup_of_le_left (le_iSup₂_of_le (⟨P, hP, hb⟩ : A) hd le_rfl)
      · exact le_sup_of_le_right (le_iSup₂_of_le P (Finset.mem_filter.2 ⟨hP, hd⟩) le_rfl)
    have h3 : ⨆ P ∈ F.filter (fun P => ¬ P ∣ p), Lk P ≤ LinearMap.ker (aeval f q) := by
      refine iSup₂_le fun P hP => ?_
      obtain ⟨hPF, hPp⟩ := Finset.mem_filter.1 hP
      have hd : P ∣ p * q := by
        rw [hpq, ← hprod]
        exact Finset.dvd_prod_of_mem _ hPF
      exact ker_le_of_dvd f (((hirr P hPF).prime.dvd_or_dvd hd).resolve_left hPp)
    have hco : IsCoprime p q := by
      rw [← hpq] at hs
      exact (squarefree_mul_iff.1 hs).1.isCoprime
    have hdis := disjoint_ker_aeval_of_isCoprime f hco
    refine le_antisymm (fun x hx => ?_) h1
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (h2 (Submodule.mem_top (x := x)))
    have hyW := h1 hy
    have hzW : z ∈ W := by simpa using W.sub_mem hx hyW
    have hz0 : z = 0 := by
      rw [hWe] at hzW
      exact (Submodule.disjoint_def.1 hdis) z hzW (h3 hz)
    rw [hz0, add_zero]
    exact hy

end Lin

section Main

open PositivityTheory.Rg.BcB.D4

theorem perp_anti {K : Type} [Field K] {n : ℕ} (σ : K →+* K) {W W' : Submodule K (Fin n → K)} (h : W ≤ W') :
    perp σ W' ≤ perp σ W := fun _ hy x hx => hy x (h hx)

theorem perpD_anti {K : Type} [Field K] {n : ℕ} (σ : K →+* K) (d : GL (Fin n) K) {W W' : Submodule K (Fin n → K)}
    (h : W ≤ W') : perpD σ d W' ≤ perpD σ d W :=
  Submodule.map_mono (perp_anti σ h)

theorem img_eq_of_invariant {K : Type} [Field K] {n : ℕ} (g : GL (Fin n) K) (W : Submodule K (Fin n → K))
    (h : ∀ x ∈ W, Matrix.toLin' g.val x ∈ W) : img g W = W := by
  have hinj : Function.Injective (Matrix.toLin' g.val) := by
    intro a b hab
    have h1 := congrArg (fun z => (g⁻¹ : GL (Fin n) K).val *ᵥ z) hab
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul] using h1
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  · exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm

theorem pairParam : PairParam := by
  intro E _ _ _ n d hd
  let f : Module.End E (Fin n → E) := Matrix.toLin' (nrm d).val
  have hcp : LinearMap.charpoly f = (nrm d).val.charpoly := by
    simp [f, Matrix.charpoly_toLin']
  have hs : Squarefree (LinearMap.charpoly f) := by
    rw [hcp]
    exact Polynomial.Separable.squarefree hd
  obtain ⟨A, hA, L, hind, hne, hinv, hall⟩ := exists_atoms f hs
  let S : Set A → Submodule E (Fin n → E) := fun I => ⨆ i ∈ I, L i
  have hSinv : ∀ I, ∀ x ∈ S I, f x ∈ S I := by
    intro I x hx
    have h1 : S I ≤ (S I).comap f := by
      refine iSup₂_le fun i hi x hx => ?_
      exact (le_iSup₂_of_le (f := fun i (_ : i ∈ I) => L i) i hi le_rfl : L i ≤ S I) (hinv i x hx)
    exact h1 hx
  have hSle : ∀ I J, S I ≤ S J ↔ I ⊆ J := by
    intro I J
    constructor
    · intro h a ha
      by_contra hc
      have h1 : L a ≤ S I := le_iSup₂_of_le (f := fun i (_ : i ∈ I) => L i) a ha le_rfl
      have h2 : S J ≤ ⨆ j, ⨆ (_ : j ≠ a), L j :=
        iSup₂_le fun j hj => le_iSup₂_of_le (f := fun j (_ : j ≠ a) => L j) j (fun e => hc (e ▸ hj)) le_rfl
      exact hne a ((hind a).eq_bot_of_le (h1.trans (h.trans h2)))
    · intro h
      exact biSup_mono h
  have hSinj : ∀ I J, S I = S J → I = J := fun I J h =>
    Set.Subset.antisymm ((hSle _ _).1 h.le) ((hSle _ _).1 h.ge)
  have hstab : ∀ I, img (nrm d) (S I) = S I := fun I => img_eq_of_invariant _ _ (hSinv I)
  have hexists : ∀ W, img (nrm d) W = W → ∃ I, W = S I := by
    intro W hW
    refine hall W fun x hx => ?_
    rw [← hW]
    exact ⟨x, hx, rfl⟩
  have hφφ : ∀ W, perpD (conjE E) d (perpD (conjE E) d W) = img (nrm d) W := fun W =>
    GlobalTheory.CompanionTheory.FlagCent.perpD_perpD (conjE E) (fun a => NumberField.IsCMField.complexConj_apply_apply E a) d W
  have hφstab : ∀ W, img (nrm d) W = W → img (nrm d) (perpD (conjE E) d W) = perpD (conjE E) d W := by
    intro W hW
    rw [← hφφ, hφφ W, hW]
  have hcex : ∀ I, ∃ J, perpD (conjE E) d (S I) = S J := fun I => hexists _ (hφstab _ (hstab I))
  choose c hc using hcex
  have hanti : Antitone c := by
    intro I J h
    refine (hSle _ _).1 ?_
    rw [← hc, ← hc]
    exact perpD_anti _ _ ((hSle _ _).2 h)
  have hcc : ∀ I, c (c I) = I := fun I => hSinj _ _ (by rw [← hc, ← hc, hφφ, hstab])
  obtain ⟨ι, hι, hcι⟩ := exists_invol c hanti hcc
  obtain ⟨m, T, hT1, hT2, hT3, hT4, hT5⟩ := exists_signs ι hι
  have hSinf : ∀ I J, S (I ∩ J) = S I ⊓ S J := by
    intro I J
    obtain ⟨Q, hQ⟩ := hall (S I ⊓ S J) fun x hx => ⟨hSinv I x hx.1, hSinv J x hx.2⟩
    have h1 : Q ⊆ I := (hSle _ _).1 (hQ.symm.le.trans inf_le_left)
    have h2 : Q ⊆ J := (hSle _ _).1 (hQ.symm.le.trans inf_le_right)
    have h3 : I ∩ J ⊆ Q := (hSle _ _).1 (by
      have : S (I ∩ J) ≤ S I ⊓ S J :=
        le_inf ((hSle _ _).2 Set.inter_subset_left) ((hSle _ _).2 Set.inter_subset_right)
      exact this.trans hQ.le)
    have h4 : I ∩ J = Q := Set.Subset.antisymm h3 (Set.subset_inter h1 h2)
    rw [h4]
    exact hQ.symm
  refine ⟨m, fun e => S (T e), fun e => ⟨hstab _, ?_⟩, fun W hW => ?_, ?_, fun e e' => ?_, fun e e' h => ?_,
    fun e => ?_⟩
  · rw [hc, hSle, hcι]
    rintro a ha ⟨b, hb, rfl⟩
    exact hT1 _ _ hb ha
  · obtain ⟨I, rfl⟩ := hexists W hW.1
    have h2 := hW.2
    rw [hc, hSle, hcι] at h2
    have h3 : ∀ a ∈ I, ι a ∉ I := fun a ha hb => h2 ha ⟨ι a, hb, hι a⟩
    obtain ⟨e, he, hu⟩ := hT2 I h3
    exact ⟨e, congrArg S he, fun e' h => hu e' (hSinj _ _ h)⟩
  · show S (T 0) = ⊥
    rw [hT3]
    simp [S]
  · show S (T (sMeet e e')) = S (T e) ⊓ S (T e')
    rw [hT4, hSinf]
  · exact (hSle _ _).2 (hT5 e e' h)
  · show perpD (conjE E) d (perpD (conjE E) d (S (T e))) = S (T e)
    rw [hφφ, hstab]

end Main

end GlobalTheory.CompanionTheory.PairParam
