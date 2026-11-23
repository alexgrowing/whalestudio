import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct

namespace GlobalTheory.LocGL

section General

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem IsSocle.twist {σ : Representation ℂ G W} {π : Representation ℂ G V} (h : IsSocle σ π) (χ : G →* ℂˣ) :
    IsSocle (SmGL.twist σ χ) (SmGL.twist π χ) := by
  obtain ⟨hi, f, hf, hS⟩ := h
  refine ⟨isIrreducible_twist hi χ, twistMap f χ, hf, fun S hS' => ?_⟩
  have hA : IsAtom (subrepTwist π χ S) := ((subrepTwist π χ).isAtom_iff S).2 hS'
  have hE := congrArg Subrepresentation.toSubmodule (hS _ hA)
  exact Subrepresentation.ext hE

theorem IsCosocle.twist {σ : Representation ℂ G W} {π : Representation ℂ G V} (h : IsCosocle σ π) (χ : G →* ℂˣ) :
    IsCosocle (SmGL.twist σ χ) (SmGL.twist π χ) := by
  obtain ⟨hi, f, hf, hS⟩ := h
  refine ⟨isIrreducible_twist hi χ, twistMap f χ, hf, fun S hS' => ?_⟩
  have hA : IsCoatom (subrepTwist π χ S) := ((subrepTwist π χ).isCoatom_iff S).2 hS'
  have hE := congrArg Subrepresentation.toSubmodule (hS _ hA)
  exact Subrepresentation.ext hE

theorem isSubquotient_twist {σ : Representation ℂ G W} {π : Representation ℂ G V} (h : IsSubquotient σ π)
    (χ : G →* ℂˣ) : IsSubquotient (twist σ χ) (twist π χ) := by
  obtain ⟨S, f, hf⟩ := h
  refine ⟨(subrepTwist π χ).symm S, ⟨f.toLinearMap, fun g => ?_⟩, hf⟩
  ext v
  have := f.isIntertwining _ _ g v
  change f ((χ g : ℂ) • (S.toRepresentation g v)) = (χ g : ℂ) • σ g (f v)
  rw [map_smul, this]

variable [TopologicalSpace G] [IsTopologicalGroup G]

def indTwistMap {P Q : Subgroup G} {σ : Representation ℂ P V} {τ : Representation ℂ Q W} (hQ : Q ≤ P)
    {χ : G →* ℂˣ} (hχ : IsSmoothChar χ) (L : V →ₗ[ℂ] W)
    (h : ∀ (q : Q) v, τ q (L v) = (χ q : ℂ) • L (σ ⟨q, hQ q.2⟩ v)) :
    smoothPart (ind P σ) →ₗ[ℂ] smoothPart (ind Q τ) where
  toFun f := ⟨⟨fun g => (χ g : ℂ) • L (f.1.1 g), fun q g => by
      have := f.1.2 ⟨q, hQ q.2⟩ g
      show (χ (q * g) : ℂ) • L (f.1.1 (q * g)) = τ q ((χ g : ℂ) • L (f.1.1 g))
      rw [map_smul, h, ← this, map_mul, Units.val_mul, smul_smul, mul_comm]⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset
      ((IsOpen.inter f.2 hχ).mem_nhds (by simp)) fun g hg => by
        have h1 : ind P σ g f.1 = f.1 := hg.1
        have h2 : χ g = 1 := hg.2
        apply Subtype.ext
        funext x
        have : f.1.1 (x * g) = f.1.1 x := congrFun (congrArg Subtype.val h1) x
        show (χ (x * g) : ℂ) • L (f.1.1 (x * g)) = (χ x : ℂ) • L (f.1.1 x)
        rw [this, map_mul, h2, mul_one])⟩
  map_add' f g := Subtype.ext (Subtype.ext (funext fun x => by simp))
  map_smul' c f := Subtype.ext (Subtype.ext (funext fun x => by simp [smul_comm c]))

def smIndTwistEquiv {P Q : Subgroup G} {σ : Representation ℂ P V} {τ : Representation ℂ Q W} (hQ : Q ≤ P) (hP : P ≤ Q)
    {χ : G →* ℂˣ} (hχ : IsSmoothChar χ) (L : V ≃ₗ[ℂ] W)
    (h : ∀ (q : Q) v, τ q (L v) = (χ q : ℂ) • L (σ ⟨q, hQ q.2⟩ v)) :
    (twist (smInd P σ) χ).Equiv (smInd Q τ) :=
  .mk (LinearEquiv.ofLinear (indTwistMap hQ hχ L.toLinearMap h)
      (indTwistMap hP hχ.inv L.symm.toLinearMap fun p w => by
        obtain ⟨v, rfl⟩ := L.surjective w
        simp [h, smul_smul])
      (LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => by
        simp [indTwistMap, smul_smul])))
      (LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => by
        simp [indTwistMap, smul_smul]))))
    fun g => LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => by
      show (χ x : ℂ) • L ((χ g : ℂ) • f.1.1 (x * g)) = (χ (x * g) : ℂ) • L (f.1.1 (x * g))
      rw [map_smul, smul_smul, map_mul, Units.val_mul]))

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

section Products

variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n]

def parIndTwistEquiv (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) V) {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    (twist (parInd e ρ) (detChar n χ)).Equiv (parInd e (twist ρ ((detChar n χ).comp (leviEmb k e)))) :=
  smIndTwistEquiv le_rfl le_rfl hχ.detChar (.refl ℂ V) fun q v => by
    show (deltaHalf k m (leviProj k e q) : ℂ) • (χ (GeneralLinearGroup.det (leviEmb k e (leviProj k e q))) : ℂ) •
        ρ (leviProj k e q) v = (χ (GeneralLinearGroup.det (q : GL n k)) : ℂ) •
          (deltaHalf k m (leviProj k e q) : ℂ) • ρ (leviProj k e q) v
    rw [det_leviEmb, det_parab, smul_comm]

def multiProdTwistEquiv (e : (Σ a, m a) ≃ n) {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (π : ∀ a, Representation ℂ (GL (m a) k) (X a)) {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    (twist (multiProd e π) (detChar n χ)).Equiv (multiProd e fun a => twist (π a) (detChar (m a) χ)) :=
  (parIndTwistEquiv e (piTensor π) hχ).trans (parIndEquiv e (.mk (.refl ℂ _) fun g => by
    ext x
    simp [det_leviEmb, MultilinearMap.map_smul_univ]))

end Products

def prodIrrTwistEquiv {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    (twist (prodIrr x hd) (detChar (Fin N) χ)).Equiv (prodIrr (fun a => (x a).tw χ hχ) hd) :=
  (multiProdTwistEquiv _ _ hχ).trans (multiProdEquiv _ fun a => (x a).twEquiv χ hχ)

theorem exists_equiv_prodIrr_tw {h N : ℕ} {x y : Fin h → IrrGL k} (hd : ∑ a, (x a).1 = N) {χ : kˣ →* ℂˣ}
    {hχ : IsSmoothChar χ} (hy : ∀ a, y a = (x a).tw χ hχ) :
    ∃ hd' : ∑ a, (y a).1 = N, Nonempty ((twist (prodIrr x hd) (detChar (Fin N) χ)).Equiv (prodIrr y hd')) := by
  obtain rfl : y = fun a => (x a).tw χ hχ := funext hy
  exact ⟨hd, ⟨prodIrrTwistEquiv x hd χ hχ⟩⟩

theorem HasSupport.tw {n : Type} [Fintype n] [DecidableEq n] {π : Representation ℂ (GL n k) V}
    {s : Multiset (IrrGL k)} (h : HasSupport π s) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    HasSupport (twist π (detChar n χ)) (s.map (·.tw χ hχ)) := by
  obtain ⟨h', x, hx, hi, hc, e, hsq⟩ := h
  refine ⟨h', fun a => (x a).tw χ hχ, ?_, isIrreducible_twist hi _, fun a => ?_, e, ?_⟩
  · rw [← hx, Multiset.map_map]; rfl
  · have hcu : (x a).IsCusp := ⟨(hc a).1, (hc a).2.2⟩
    exact ⟨(hcu.tw χ hχ).1, ((x a).tw χ hχ).2.rep.irr, (hcu.tw χ hχ).2⟩
  · have E := (multiProdTwistEquiv e (fun a => (x a).rep) hχ).trans
      (multiProdEquiv e fun a => (x a).twEquiv χ hχ)
    exact (isSubquotient_twist hsq _).trans (IsSubquotient.of_injective E.toIntertwiningMap
      E.toLinearEquiv.injective)

theorem IrrGL.tw_nu (x : IrrGL k) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (s : ℂ) :
    (x.tw χ hχ).nu s = (x.nu s).tw χ hχ := by
  unfold nu
  rw [tw_tw, tw_tw]
  congr 1
  exact mul_comm _ _

theorem IrrGL.tw_tw_inv (x : IrrGL k) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : (x.tw χ hχ).tw χ⁻¹ hχ.inv = x := by
  have key : ∀ (ψ : kˣ →* ℂˣ) (hψ : IsSmoothChar ψ), ψ = 1 → x.tw ψ hψ = x := by
    rintro ψ hψ rfl
    exact tw_one x hψ
  rw [tw_tw]
  exact key _ _ (mul_inv_cancel χ)

theorem IrrGL.tw_injective (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    Function.Injective fun x : IrrGL k => x.tw χ hχ := by
  intro x y h
  have h' : x.tw χ hχ = y.tw χ hχ := h
  rw [← tw_tw_inv x χ hχ, h', tw_tw_inv]

private theorem segment_tw_first (Δ : Segment k) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    (Δ.tw χ hχ).first = Δ.first.tw χ hχ :=
  Segment.first_ofFirst _ _ _ _

end GlobalTheory.LocGL

namespace GlobalTheory.SmGL.Segment

open GlobalTheory.LocGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem term_tw (Δ : Segment k) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (a : Fin Δ.len) :
    (Δ.tw χ hχ).term a = (Δ.term a).tw χ hχ := by
  unfold term
  rw [segment_tw_first]
  exact IrrGL.tw_nu _ _ _ _

theorem carrier_tw (Δ : Segment k) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    (Δ.tw χ hχ).carrier = (fun x => x.tw χ hχ) '' Δ.carrier := by
  unfold carrier
  rw [← Set.range_comp]
  exact congrArg Set.range (funext fun a => term_tw Δ χ hχ a)

theorem tw_tw_inv (Δ : Segment k) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : (Δ.tw χ hχ).tw χ⁻¹ hχ.inv = Δ := by
  apply ext_first
  · rw [segment_tw_first, segment_tw_first, IrrGL.tw_tw_inv]
  · rfl

theorem Linked.tw {Δ Δ' : Segment k} (h : Linked Δ Δ') (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    Linked (Δ.tw χ hχ) (Δ'.tw χ hχ) := by
  obtain ⟨⟨Γ, hΓ⟩, h1, h2⟩ := h
  have hinj := IrrGL.tw_injective χ hχ
  refine ⟨⟨Γ.tw χ hχ, ?_⟩, ?_, ?_⟩
  · rw [carrier_tw, carrier_tw, carrier_tw, hΓ, Set.image_union]
  · rwa [carrier_tw, carrier_tw, Set.image_subset_image_iff hinj]
  · rwa [carrier_tw, carrier_tw, Set.image_subset_image_iff hinj]

theorem Precedes.tw {Δ Δ' : Segment k} (h : Precedes Δ Δ') (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    Precedes (Δ.tw χ hχ) (Δ'.tw χ hχ) := by
  obtain ⟨hl, j, hj, he⟩ := h
  refine ⟨hl.tw χ hχ, j, hj, ?_⟩
  rw [segment_tw_first, segment_tw_first, he, IrrGL.tw_nu]

theorem linked_tw_iff {Δ Δ' : Segment k} (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    Linked (Δ.tw χ hχ) (Δ'.tw χ hχ) ↔ Linked Δ Δ' := by
  refine ⟨fun h => ?_, fun h => h.tw χ hχ⟩
  have := h.tw χ⁻¹ hχ.inv
  rwa [tw_tw_inv, tw_tw_inv] at this

theorem precedes_tw_iff {Δ Δ' : Segment k} (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    Precedes (Δ.tw χ hχ) (Δ'.tw χ hχ) ↔ Precedes Δ Δ' := by
  refine ⟨fun h => ?_, fun h => h.tw χ hχ⟩
  have := h.tw χ⁻¹ hχ.inv
  rwa [tw_tw_inv, tw_tw_inv] at this

end GlobalTheory.SmGL.Segment

namespace GlobalTheory.LocGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {N : ℕ}

section Classifications

variable {π : Representation ℂ (GL (Fin N) k) V} {Δ : Segment k} {𝔪 : Multiset (Segment k)}

theorem IsZSeg.tw (h : IsZSeg Δ π) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    IsZSeg (Δ.tw χ hχ) (twist π (detChar (Fin N) χ)) := by
  obtain ⟨hd, hs⟩ := h
  obtain ⟨hd', ⟨E⟩⟩ := exists_equiv_prodIrr_tw (y := (Δ.tw χ hχ).term) hd (hχ := hχ)
    (fun a => Segment.term_tw Δ χ hχ a)
  exact ⟨hd', (hs.twist _).of_equiv (.refl _) E⟩

theorem IsLSeg.tw (h : IsLSeg Δ π) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    IsLSeg (Δ.tw χ hχ) (twist π (detChar (Fin N) χ)) := by
  obtain ⟨hd, hs⟩ := h
  obtain ⟨hd', ⟨E⟩⟩ := exists_equiv_prodIrr_tw (y := (Δ.tw χ hχ).term) hd (hχ := hχ)
    (fun a => Segment.term_tw Δ χ hχ a)
  exact ⟨hd', (hs.twist _).of_equiv (.refl _) E⟩

theorem IsOrderedForm.tw {h : ℕ} {Δ : Fin h → Segment k} (H : IsOrderedForm Δ 𝔪) (χ : kˣ →* ℂˣ)
    (hχ : IsSmoothChar χ) : IsOrderedForm (fun i => (Δ i).tw χ hχ) (𝔪.map (·.tw χ hχ)) := by
  obtain ⟨hm, hp⟩ := H
  refine ⟨?_, fun i j hij => ?_⟩
  · rw [← hm, Multiset.map_map]; rfl
  · rw [Segment.precedes_tw_iff]; exact hp i j hij

theorem ZFactors.tw {h : ℕ} {x : Fin h → IrrGL k} (H : ZFactors 𝔪 x) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    ZFactors (𝔪.map (·.tw χ hχ)) fun a => (x a).tw χ hχ := by
  obtain ⟨Δ, hΔ, hz⟩ := H
  exact ⟨fun i => (Δ i).tw χ hχ, hΔ.tw χ hχ, fun i => ((hz i).tw χ hχ).of_equiv ((x i).twEquiv χ hχ)⟩

theorem LFactors.tw {h : ℕ} {x : Fin h → IrrGL k} (H : LFactors 𝔪 x) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    LFactors (𝔪.map (·.tw χ hχ)) fun a => (x a).tw χ hχ := by
  obtain ⟨Δ, hΔ, hz⟩ := H
  exact ⟨fun i => (Δ i).tw χ hχ, hΔ.tw χ hχ, fun i => ((hz i).tw χ hχ).of_equiv ((x i).twEquiv χ hχ)⟩

theorem IsZ.tw (h : IsZ 𝔪 π) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    IsZ (𝔪.map (·.tw χ hχ)) (twist π (detChar (Fin N) χ)) := by
  obtain ⟨h', x, hd, hz, hs⟩ := h
  exact ⟨h', fun a => (x a).tw χ hχ, hd, hz.tw χ hχ,
    (hs.twist _).of_equiv (.refl _) (prodIrrTwistEquiv x hd χ hχ)⟩

theorem IsL.tw (h : IsL 𝔪 π) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    IsL (𝔪.map (·.tw χ hχ)) (twist π (detChar (Fin N) χ)) := by
  obtain ⟨h', x, hd, hz, hs⟩ := h
  exact ⟨h', fun a => (x a).tw χ hχ, hd, hz.tw χ hχ,
    (hs.twist _).of_equiv (.refl _) (prodIrrTwistEquiv x hd χ hχ)⟩

theorem IsSpeh.tw {x : IrrGL k} {d : ℕ} (h : IsSpeh x d π) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    IsSpeh (x.tw χ hχ) d (twist π (detChar (Fin N) χ)) := by
  obtain ⟨hd, hs⟩ := h
  obtain ⟨hd', ⟨E⟩⟩ := exists_equiv_prodIrr_tw (y := spehFactor (x.tw χ hχ) d) hd (hχ := hχ)
    (fun a => IrrGL.tw_nu x χ hχ _)
  exact ⟨hd', (hs.twist _).of_equiv (.refl _) E⟩

end Classifications

theorem nonempty_prod₂_equiv_multiProd {d : Fin 2 → ℕ} (hd : ∑ a, d a = d 0 + d 1) {X : Fin 2 → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) :
    Nonempty ((prod₂ (π 0) (π 1)).Equiv (multiProd (stdBlocks d hd) π)) := by
  have e0 : ∀ i : Fin (d 0), stdBlocks d hd ⟨0, i⟩ = two (stdSum (rfl : d 0 + d 1 = d 0 + d 1)) ⟨false, i⟩ := by
    intro i
    apply Fin.ext
    rw [stdBlocks_val, two_false, stdSum_inl, Finset.sum_eq_zero (fun b _ => absurd b.2 (by simp)), zero_add]
  have e1 : ∀ j : Fin (d 1), stdBlocks d hd ⟨1, j⟩ = two (stdSum (rfl : d 0 + d 1 = d 0 + d 1)) ⟨true, j⟩ := by
    intro j
    apply Fin.ext
    rw [stdBlocks_val, two_true, stdSum_inr, Finset.sum_eq_single (⟨0, by simp⟩ : Fin (1 : Fin 2))]
    · rfl
    · intro b _ hb
      exact absurd (Fin.ext (by simpa using b.2)) hb
    · intro h
      exact absurd (Finset.mem_univ _) h
  have e0' : ∀ (h : 0 < 2) (i : Fin (d ⟨0, h⟩)),
      stdBlocks d hd ⟨⟨0, h⟩, i⟩ = two (stdSum (rfl : d 0 + d 1 = d 0 + d 1)) ⟨false, i⟩ := fun _ i => e0 i
  have e1' : ∀ (h : 1 < 2) (i : Fin (d ⟨1, h⟩)),
      stdBlocks d hd ⟨⟨1, h⟩, i⟩ = two (stdSum (rfl : d 0 + d 1 = d 0 + d 1)) ⟨true, i⟩ := fun _ i => e1 i
  have hQP : parab k (stdBlocks d hd) ≤ parab k (two (stdSum (rfl : d 0 + d 1 = d 0 + d 1))) := by
    intro g hg
    rw [mem_parab_iff] at hg ⊢
    intro a b i j hab
    cases a <;> cases b
    · exact absurd hab (by decide)
    · exact absurd hab (by decide)
    · have := hg 1 0 i j (by decide)
      rwa [e1, e0] at this
    · exact absurd hab (by decide)
  have hPQ : parab k (two (stdSum (rfl : d 0 + d 1 = d 0 + d 1))) ≤ parab k (stdBlocks d hd) := by
    intro g hg
    rw [mem_parab_iff] at hg ⊢
    intro a b i j hab
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    have hab' : b < a := hab
    obtain rfl : a = 1 := by omega
    obtain rfl : b = 0 := by omega
    have := hg true false i j (by decide)
    rw [e1' ha i, e0' hb j]
    exact this
  have b0 : ∀ q : parab k (stdBlocks d hd), leviProj k (stdBlocks d hd) q 0 =
      (leviProj k (two (stdSum (rfl : d 0 + d 1 = d 0 + d 1))) ⟨q, hQP q.2⟩ false : GL (Fin (d 0)) k) := by
    intro q
    ext i j
    simp only [leviProj_apply, e0]
  have b1 : ∀ q : parab k (stdBlocks d hd), leviProj k (stdBlocks d hd) q 1 =
      (leviProj k (two (stdSum (rfl : d 0 + d 1 = d 0 + d 1))) ⟨q, hQP q.2⟩ true : GL (Fin (d 1)) k) := by
    intro q
    ext i j
    simp only [leviProj_apply, e1]
  have m0 : modExp (fun a : Fin 2 => Fin (d a)) 0 = d 1 := by
    simp [modExp, Finset.sum_filter, Fin.sum_univ_two]
  have m1 : modExp (fun a : Fin 2 => Fin (d a)) 1 = -(d 0 : ℤ) := by
    simp [modExp, Finset.sum_filter, Fin.sum_univ_two]
  have hδ : ∀ q : parab k (stdBlocks d hd), deltaHalf k (fun a : Fin 2 => Fin (d a)) (leviProj k (stdBlocks d hd) q) =
      deltaHalf k (Two (Fin (d 0)) (Fin (d 1)))
        (leviProj k (two (stdSum (rfl : d 0 + d 1 = d 0 + d 1))) ⟨q, hQP q.2⟩) := by
    intro q
    rw [← (leviTwo k (Fin (d 0)) (Fin (d 1))).apply_symm_apply
      (leviProj k (two (stdSum (rfl : d 0 + d 1 = d 0 + d 1))) ⟨q, hQP q.2⟩), deltaHalf_two,
      deltaHalf_apply, Fin.prod_univ_two, m0, m1, b0 q, b1 q]
    simp only [Fintype.card_fin, Int.cast_neg, Int.cast_natCast]
    rfl
  let L : X 0 ⊗[ℂ] X 1 ≃ₗ[ℂ] ⨂[ℂ] i, X i :=
    (TensorProduct.congr (LinearEquiv.refl ℂ (X 0))
      (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun j : Fin 1 => X j.succ) 0).symm).trans
      (MultiIrr.tensorCons X)
  have hL : ∀ (x : X 0) (y : X 1), L (x ⊗ₜ y) =
      PiTensorProduct.tprod ℂ (Fin.cons x fun i => Function.update (0 : ∀ j : Fin 1, X j.succ) 0 y i) := by
    intro x y
    simp only [L, LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply]
    rw [PiTensorProduct.subsingletonEquiv_symm_apply]
    erw [MultiIrr.tensorCons_tmul]
    congr
    funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    simp only [Function.update_self]
  suffices hc : ∀ (q : parab k (stdBlocks d hd)) (v : X 0 ⊗[ℂ] X 1),
      (twist (piTensor π) (deltaHalf k fun a : Fin 2 => Fin (d a))).comp (leviProj k (stdBlocks d hd)) q (L v) =
        ((1 : GL (Fin (d 0 + d 1)) k →* ℂˣ) q : ℂ) • L
          ((twist ((extTensor (π 0) (π 1)).comp (leviTwo k (Fin (d 0)) (Fin (d 1))).symm.toMonoidHom)
            (deltaHalf k (Two (Fin (d 0)) (Fin (d 1))))).comp
              (leviProj k (two (stdSum (rfl : d 0 + d 1 = d 0 + d 1)))) ⟨q, hQP q.2⟩ v) by
    have key := smIndTwistEquiv hQP hPQ isSmoothChar_one L hc
    rw [twist_one] at key
    exact ⟨key⟩
  intro q v
  rw [MonoidHom.one_apply, Units.val_one, one_smul]
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul x y =>
    rw [hL]
    simp only [MonoidHom.comp_apply, twist_apply]
    rw [map_smul, ← hδ q]
    congr 1
    rw [piTensor_tprod, extTensor_tmul, hL]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      rw [b0 q]
      rfl
    · obtain rfl : j = 0 := Subsingleton.elim _ _
      simp only [Fin.cons_succ, Function.update_self]
      show π 1 (leviProj k (stdBlocks d hd) q 1) y = _
      rw [b1 q]
      rfl

theorem nonempty_prod₂_equiv_prodIrr_rep (x : Fin 2 → IrrGL k) (hd : ∑ a, (x a).1 = (x 0).1 + (x 1).1) :
    Nonempty ((prod₂ (x 0).rep (x 1).rep).Equiv (prodIrr x hd)) :=
  nonempty_prod₂_equiv_multiProd hd fun a => (x a).rep

theorem nonempty_prod₂_equiv_prodIrr_pair (y z : IrrGL k) (hd : ∑ a, (![y, z] a).1 = y.1 + z.1) :
    Nonempty ((prod₂ y.rep z.rep).Equiv (prodIrr ![y, z] hd)) :=
  nonempty_prod₂_equiv_prodIrr_rep ![y, z] hd

def prod₂Equiv {r t : ℕ} {V' W' : Type} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    {π₁ : Representation ℂ (GL (Fin r) k) V} {π₂ : Representation ℂ (GL (Fin t) k) W}
    {σ₁ : Representation ℂ (GL (Fin r) k) V'} {σ₂ : Representation ℂ (GL (Fin t) k) W'}
    (φ₁ : π₁.Equiv σ₁) (φ₂ : π₂.Equiv σ₂) : (prod₂ π₁ π₂).Equiv (prod₂ σ₁ σ₂) :=
  parIndEquiv _ (compEquiv (ρ := extTensor π₁ π₂) (σ := extTensor σ₁ σ₂)
    (.mk (TensorProduct.congr φ₁.toLinearEquiv φ₂.toLinearEquiv) fun g => by
      ext v w
      exact congrArg₂ (fun a b => a ⊗ₜ[ℂ] b) (φ₁.toIntertwiningMap.isIntertwining _ _ g.1 v)
        (φ₂.toIntertwiningMap.isIntertwining _ _ g.2 w)) _)

theorem nonempty_prod₂_equiv_prodIrr {r t : ℕ} (π₁ : Representation ℂ (GL (Fin r) k) V) (s₁ : IsSmooth π₁)
    (i₁ : π₁.IsIrreducible) (π₂ : Representation ℂ (GL (Fin t) k) W) (s₂ : IsSmooth π₂) (i₂ : π₂.IsIrreducible)
    (hd : ∑ a, (![IrrGL.of π₁ s₁ i₁, IrrGL.of π₂ s₂ i₂] a).1 = r + t) :
    Nonempty ((prod₂ π₁ π₂).Equiv (prodIrr ![IrrGL.of π₁ s₁ i₁, IrrGL.of π₂ s₂ i₂] hd)) := by
  obtain ⟨E⟩ := nonempty_prod₂_equiv_prodIrr_pair (IrrGL.of π₁ s₁ i₁) (IrrGL.of π₂ s₂ i₂) hd
  exact ⟨(prod₂Equiv (IrrGL.equivOf π₁ s₁ i₁) (IrrGL.equivOf π₂ s₂ i₂)).trans E⟩

end GlobalTheory.LocGL
