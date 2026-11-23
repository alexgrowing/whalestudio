import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import ReciprocityTheory.DualLattices.MemDualLat
import ReciprocityTheory.DualLattices.IsUnitDetOfSpanEq
import ReciprocityTheory.DualLattices.PowMemCarrier
import ReciprocityTheory.DualLattices.HasLenCokerDet
import ReciprocityTheory.DualLattices.MemOfSumSingleEqZero
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes

noncomputable section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Re

theorem stabadd : ∀ (C : Type) [Field C] (R : Type) [CommRing R] [Algebra R C], ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'], ∀ (AA : HopfOrder (C := C) R N) (AA' : HopfOrder (C := C) R N') (e e' : N →+ N'), (∀ g ∈ AA'.carrier, (fun x => g (e x)) ∈ AA.carrier) → (∀ g ∈ AA'.carrier, (fun x => g (e' x)) ∈ AA.carrier) → (∀ g ∈ AA'.carrier, (fun x => g (e x + e' x)) ∈ AA.carrier) ∧ (∀ g ∈ AA'.carrier, (fun x => g (e x - e' x)) ∈ AA.carrier) := by
  intro C _ R _ _ N _ _ _ N' _ _ _ AA AA' e e' he he'
  have key : ∀ a b : N → N', (∀ g ∈ AA'.carrier, (fun x => g (a x)) ∈ AA.carrier) →
      (∀ g ∈ AA'.carrier, (fun x => g (b x)) ∈ AA.carrier) →
      ∀ g ∈ AA'.carrier, (fun x => g (a x + b x)) ∈ AA.carrier := by
    intro a b ha hb g hg
    have h : (tensorSpan R AA'.carrier).map
        (LinearMap.funLeft R C (fun x : N => (a x, b x))) ≤ AA.carrier := by
      rw [tensorSpan, Submodule.map_span_le]
      rintro F ⟨u, hu, w, hw, rfl⟩
      exact AA.mul_mem _ _ (ha u hu) (hb w hw)
    exact h (Submodule.mem_map_of_mem (AA'.comul g hg))
  refine ⟨key e e' he he', fun g hg => ?_⟩
  have := key e (fun x => - e' x) he (fun g hg => he' _ (AA'.antipode g hg)) g hg
  simpa only [sub_eq_add_neg] using this

theorem ret_hopf : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'], ∀ (ι : N' →+ N) (π : N →+ N'), (∀ y, π (ι y) = y) → (∀ g ∈ AA.carrier, (fun x => g (ι (π x))) ∈ AA.carrier) → (∃ A' : HopfOrder (C := C) R N', A'.carrier = AA.carrier.map (LinearMap.funLeft R C (ι : N' → N))) ∧ (∀ h ∈ AA.carrier.map (LinearMap.funLeft R C (ι : N' → N)), (fun x => h (π x)) ∈ AA.carrier) ∧ ∀ K' : AddSubgroup N', GenAF p AA.carrier (K'.map ι) → GenAF p (AA.carrier.map (LinearMap.funLeft R C (ι : N' → N))) K' := by
  intro p _ C _ _ _ v R _ _ hv hp N _ _ _ AA N' _ _ _ ι π hπ hst
  classical
  have hinj : Function.Injective ι := fun a b h => by rw [← hπ a, h, hπ b]
  have hpull : ∀ h ∈ AA.carrier.map (LinearMap.funLeft R C (ι : N' → N)),
      (fun x => h (π x)) ∈ AA.carrier := by
    rintro h ⟨g, hg, rfl⟩
    exact hst g hg
  refine ⟨?_, hpull, ?_⟩
  · letI : Fintype ι.range := AddSubgroup.instFintypeSubtypeMemOfDecidablePred ι.range
    obtain ⟨⟨AK, hAK⟩, -⟩ := h2 C R v hv N ι.range AA
    refine ⟨hopfPull (AddMonoidHom.ofInjective hinj) AK, ?_⟩
    show AK.carrier.map _ = _
    rw [hAK, ← Submodule.map_comp]
    rfl
  · intro K' hG h hh
    have h1 : (fun x => h (π x)) ∈ invFun AA.carrier (K'.map ι) := by
      refine ⟨hpull h hh.1, ?_⟩
      rintro x k ⟨k', hk', rfl⟩
      show h (π (x + ι k')) = h (π x)
      rw [map_add, hπ]
      exact hh.2 _ _ hk'
    have h2 := hG h1
    let φ : (N → C) →ₐ[R] (N' → C) := AlgHom.pi (fun y => Pi.evalAlgHom R (fun _ : N => C) (ι y))
    have hφ : ∀ g y, φ g y = g (ι y) := fun _ _ => rfl
    have h3 : φ (fun x => h (π x)) = h := by
      funext y; rw [hφ]; simp only [hπ]
    have h4 : (Algebra.adjoin R ((afFun p (invFun AA.carrier (K'.map ι)) : Submodule R (N → C)) :
        Set (N → C))).map φ ≤ Algebra.adjoin R ((afFun p (invFun (AA.carrier.map
          (LinearMap.funLeft R C (ι : N' → N))) K') : Submodule R (N' → C)) : Set (N' → C)) := by
      rw [AlgHom.map_adjoin]
      refine Algebra.adjoin_mono ?_
      rintro _ ⟨g, ⟨⟨hg1, hg2⟩, hg3⟩, rfl⟩
      refine ⟨⟨⟨g, hg1, rfl⟩, fun y k hk => ?_⟩, fun x y => ?_⟩
      · rw [hφ, hφ, map_add]; exact hg2 _ _ ⟨k, hk, rfl⟩
      · rw [hφ, hφ, hφ, map_add]; exact hg3 _ _
    rw [← h3]
    exact h4 ⟨_, h2, rfl⟩

section Gen

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem hasLen_equiv {v : Valuation C NNReal} {A B : Type} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (e : A ≃ₗ[R] B) {x : NNReal} (h : HasLen v R B x) :
    HasLen v R A x :=
  h.imp fun _ h => h.imp fun _ h => ⟨h.1.map e.trans, h.2⟩

theorem hasLen_prod {v : Valuation C NNReal} (hv : v.Integers R) {A B : Type} [AddCommGroup A]
    [Module R A] [AddCommGroup B] [Module R B] {a b : NNReal} (ha : HasLen v R A a)
    (hb : HasLen v R B b) : HasLen v R (A × B) (a * b) :=
  hasLen_ext (fun κ _ _ X => hasLen_coker_det' v R hv κ X) (LinearMap.inl R A B)
    (LinearMap.snd R A B) LinearMap.inl_injective LinearMap.snd_surjective
    (LinearMap.range_inl R A B) ha hb

theorem hasColen_unique {v : Valuation C NNReal} (hv : v.Integers R) {X : Type} [Fintype X]
    [DecidableEq X] {M : Submodule R (X → C)} (hM : IsLat R M) {c c' : NNReal}
    (h : HasColen R v M c) (h' : HasColen R v M c') : c = c' := by
  obtain ⟨P, hP, hM⟩ := hM
  obtain ⟨B, hB, rfl⟩ := h
  obtain ⟨B', hB', rfl⟩ := h'
  rw [valuation_det_eq_of_span_eq_alt hv hP (hM.symm.trans hB), valuation_det_eq_of_span_eq_alt hv hP (hM.symm.trans hB')]

theorem split_equiv {N N₁ N₂ : Type} (i₁ : N₁ → N) (q₁ : N → N₁) (i₂ : N₂ → N) (q₂ : N → N₂)
    (L S : Submodule R (N → C)) (L₁ S₁ : Submodule R (N₁ → C)) (L₂ S₂ : Submodule R (N₂ → C))
    (hq₁ : ∀ y, q₁ (i₁ y) = y) (hq₂ : ∀ y, q₂ (i₂ y) = y)
    (rL₁ : ∀ g ∈ L, (fun y => g (i₁ y)) ∈ L₁) (rL₂ : ∀ g ∈ L, (fun y => g (i₂ y)) ∈ L₂)
    (rS₁ : ∀ g ∈ S, (fun y => g (i₁ y)) ∈ S₁) (rS₂ : ∀ g ∈ S, (fun y => g (i₂ y)) ∈ S₂)
    (sL₁ : ∀ h ∈ L₁, (fun x => h (q₁ x)) ∈ L) (sL₂ : ∀ h ∈ L₂, (fun x => h (q₂ x)) ∈ L)
    (sS₁ : ∀ h ∈ S₁, (fun x => h (q₁ x)) ∈ S) (sS₂ : ∀ h ∈ S₂, (fun x => h (q₂ x)) ∈ S)
    (c₁ : ∀ h ∈ L₂, (fun y => h (q₂ (i₁ y))) ∈ S₁) (c₂ : ∀ h ∈ L₁, (fun y => h (q₁ (i₂ y))) ∈ S₂)
    (dec : ∀ g ∈ L, (fun x => g x - g (i₁ (q₁ x)) - g (i₂ (q₂ x))) ∈ S) :
    Nonempty ((L ⧸ S.comap L.subtype) ≃ₗ[R]
      ((L₁ ⧸ S₁.comap L₁.subtype) × (L₂ ⧸ S₂.comap L₂.subtype))) := by
  let r₁ : L →ₗ[R] L₁ := (LinearMap.funLeft R C i₁).restrict rL₁
  let r₂ : L →ₗ[R] L₂ := (LinearMap.funLeft R C i₂).restrict rL₂
  let φ := LinearMap.prod ((S₁.comap L₁.subtype).mkQ ∘ₗ r₁) ((S₂.comap L₂.subtype).mkQ ∘ₗ r₂)
  have hφ : ∀ g, φ g = (Submodule.Quotient.mk (r₁ g), Submodule.Quotient.mk (r₂ g)) :=
    fun _ => rfl
  have hsurj : Function.Surjective φ := by
    rintro ⟨a, b⟩
    obtain ⟨⟨h₁, hh₁⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨⟨h₂, hh₂⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    refine ⟨⟨_, L.add_mem (sL₁ h₁ hh₁) (sL₂ h₂ hh₂)⟩, ?_⟩
    rw [hφ]
    refine Prod.ext ?_ ?_
    · refine (Submodule.Quotient.eq _).2 ?_
      rw [Submodule.mem_comap]
      convert c₁ h₂ hh₂ using 1
      funext y
      show h₁ (q₁ (i₁ y)) + h₂ (q₂ (i₁ y)) - h₁ y = _
      rw [hq₁]; ring
    · refine (Submodule.Quotient.eq _).2 ?_
      rw [Submodule.mem_comap]
      convert c₂ h₁ hh₁ using 1
      funext y
      show h₁ (q₁ (i₂ y)) + h₂ (q₂ (i₂ y)) - h₂ y = _
      rw [hq₂]; ring
  have hker : S.comap L.subtype = LinearMap.ker φ := by
    ext ⟨g, hg⟩
    rw [LinearMap.mem_ker, hφ, Prod.mk_eq_zero, Submodule.Quotient.mk_eq_zero,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_comap,
      Submodule.mem_comap]
    constructor
    · intro h
      exact ⟨rS₁ g h, rS₂ g h⟩
    · rintro ⟨h₁, h₂⟩
      have := S.add_mem (S.add_mem (dec g hg) (sS₁ _ h₁)) (sS₂ _ h₂)
      convert this using 1
      funext x
      show g x = g x - g (i₁ (q₁ x)) - g (i₂ (q₂ x)) + g (i₁ (q₁ x)) + g (i₂ (q₂ x))
      ring
  exact ⟨(Submodule.quotEquivOfEq _ _ hker).trans (φ.quotKerEquivOfSurjective hsurj)⟩

theorem mem_pFun {p : ℕ} {X : Type} {f : X → C} :
    f ∈ pFun (C := C) R p X ↔ ∀ x, f x ∈ pInt (C := C) R p := by
  simp [pFun, Submodule.mem_pi]

theorem addFun_comp {p : ℕ} {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (e : X →+ Y)
    {f : Y → C} (hf : f ∈ addFun (C := C) R p Y) : (fun x => f (e x)) ∈ addFun (C := C) R p X := by
  intro x y
  simp only [map_add]
  exact hf _ _

theorem linFun_comp {p : ℕ} {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (e : X →+ Y)
    {f : Y → C} (hf : f ∈ linFun (C := C) R p Y) : (fun x => f (e x)) ∈ linFun (C := C) R p X :=
  ⟨fun x => hf.1 (e x), addFun_comp e hf.2⟩

theorem afp_comp {p : ℕ} {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (e : X →+ Y)
    {M : Submodule R (X → C)} {M' : Submodule R (Y → C)} (h : ∀ g ∈ M', (fun x => g (e x)) ∈ M) :
    ∀ f ∈ afFun p M' ⊔ pFun R p Y, (fun x => f (e x)) ∈ afFun p M ⊔ pFun R p X := by
  intro f hf
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hf
  exact Submodule.add_mem_sup (show (fun x => a (e x)) ∈ afFun p M from
    ⟨h a ha.1, addFun_comp e ha.2⟩) (mem_pFun.2 fun x => mem_pFun.1 hb (e x))

theorem addFun_zero {p : ℕ} {X : Type} [AddCommGroup X] {f : X → C}
    (hf : f ∈ addFun (C := C) R p X) : f 0 ∈ pInt (C := C) R p := by
  have := Submodule.neg_mem _ (hf 0 0)
  simpa using this

theorem aug_comp {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (e : X →+ Y)
    {M : Submodule R (X → C)} {M' : Submodule R (Y → C)} (h : ∀ g ∈ M', (fun x => g (e x)) ∈ M) :
    ∀ f ∈ augIdeal M', (fun x => f (e x)) ∈ augIdeal M := by
  intro f hf
  rw [mem_aug] at hf ⊢
  exact ⟨h f hf.1, by simp only [map_zero]; exact hf.2⟩

theorem sq_comp {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (e : X →+ Y)
    {M : Submodule R (X → C)} {M' : Submodule R (Y → C)} (h : ∀ g ∈ M', (fun x => g (e x)) ∈ M) :
    ∀ f ∈ sqIdeal (augIdeal M'), (fun x => f (e x)) ∈ sqIdeal (augIdeal M) := by
  intro f hf
  have h1 : (sqIdeal (augIdeal M')).map (LinearMap.funLeft R C (e : X → Y)) ≤
      sqIdeal (augIdeal M) := by
    rw [sqIdeal, Submodule.map_span_le]
    rintro s ⟨a, ha, b, hb, rfl⟩
    exact Submodule.subset_span ⟨_, aug_comp e h a ha, _, aug_comp e h b hb, rfl⟩
  exact h1 (Submodule.mem_map_of_mem hf)

theorem sub_const_aug {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (AA : HopfOrder (C := C) R N) {u : N → C} (hu : u ∈ AA.carrier) :
    (fun x => u x - u 0) ∈ augIdeal AA.carrier := by
  obtain ⟨r, hr⟩ := AA.le_int hu 0
  rw [mem_aug]
  refine ⟨?_, sub_self _⟩
  convert AA.carrier.sub_mem hu (AA.carrier.smul_mem r AA.one_mem) using 1
  funext x
  simp [Algebra.smul_def, hr]

theorem aug_dec {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (AA : HopfOrder (C := C) R N) (a b : N →+ N)
    (ha : ∀ g ∈ AA.carrier, (fun x => g (a x)) ∈ AA.carrier)
    (hb : ∀ g ∈ AA.carrier, (fun x => g (b x)) ∈ AA.carrier) {g : N → C}
    (hg : g ∈ augIdeal AA.carrier) :
    (fun x => g (a x + b x) - g (a x) - g (b x)) ∈ sqIdeal (augIdeal AA.carrier) := by
  let T : (N × N → C) →ₗ[R] (N → C) :=
    LinearMap.funLeft R C (fun x : N => (a x, b x)) - LinearMap.funLeft R C (fun x : N => (a x, 0))
      - LinearMap.funLeft R C (fun x : N => (0, b x)) + LinearMap.funLeft R C (fun _ : N => (0, 0))
  have hT : ∀ F x, T F x = F (a x, b x) - F (a x, 0) - F (0, b x) + F (0, 0) := fun _ _ => rfl
  have h : (tensorSpan R AA.carrier).map T ≤ sqIdeal (augIdeal AA.carrier) := by
    rw [tensorSpan, Submodule.map_span_le]
    rintro F ⟨u, hu, w, hw, rfl⟩
    refine Submodule.subset_span ⟨_, sub_const_aug AA (ha u hu), _, sub_const_aug AA (hb w hw), ?_⟩
    funext x
    rw [hT]
    simp only [Pi.mul_apply, map_zero]
    ring
  rw [mem_aug] at hg
  convert h (Submodule.mem_map_of_mem (AA.comul g hg.1)) using 1
  funext x
  rw [hT]
  simp [addPull, hg.2]

end Gen

theorem ret_af : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ (N₁ : Type) [AddCommGroup N₁] [Fintype N₁] [DecidableEq N₁], ∀ (N₂ : Type) [AddCommGroup N₂] [Fintype N₂] [DecidableEq N₂], ∀ (ι₁ : N₁ →+ N) (π₁ : N →+ N₁) (ι₂ : N₂ →+ N) (π₂ : N →+ N₂), (∀ y, π₁ (ι₁ y) = y) → (∀ y, π₂ (ι₂ y) = y) → (∀ x, ι₁ (π₁ x) + ι₂ (π₂ x) = x) → (∀ y, π₁ (ι₂ y) = 0) → (∀ y, π₂ (ι₁ y) = 0) → (∀ g ∈ AA.carrier, (fun x => g (ι₁ (π₁ x))) ∈ AA.carrier) → (∀ g ∈ AA.carrier, (fun x => g (ι₂ (π₂ x))) ∈ AA.carrier) → ∀ a b, HasLen v R (AFQuot p (AA.carrier.map (LinearMap.funLeft R C (ι₁ : N₁ → N)))) a → HasLen v R (AFQuot p (AA.carrier.map (LinearMap.funLeft R C (ι₂ : N₂ → N)))) b → HasLen v R (AFQuot p AA.carrier) (a * b) := by
  intro p _ C _ _ _ v R _ _ hv hp N _ _ _ AA N₁ _ _ _ N₂ _ _ _ ι₁ π₁ ι₂ π₂ h11 h22 hsum h12 h21
    hs₁ hs₂ a b ha hb
  obtain ⟨e⟩ := split_equiv ι₁ π₁ ι₂ π₂ (linFun (C := C) R p N) (afFun p AA.carrier ⊔ pFun R p N)
    (linFun (C := C) R p N₁)
    (afFun p (AA.carrier.map (LinearMap.funLeft R C (ι₁ : N₁ → N))) ⊔ pFun R p N₁)
    (linFun (C := C) R p N₂)
    (afFun p (AA.carrier.map (LinearMap.funLeft R C (ι₂ : N₂ → N))) ⊔ pFun R p N₂) h11 h22
    (fun g hg => linFun_comp ι₁ hg) (fun g hg => linFun_comp ι₂ hg)
    (afp_comp ι₁ fun g hg => ⟨g, hg, rfl⟩) (afp_comp ι₂ fun g hg => ⟨g, hg, rfl⟩)
    (fun g hg => linFun_comp π₁ hg) (fun g hg => linFun_comp π₂ hg)
    (afp_comp π₁ (by rintro _ ⟨g, hg, rfl⟩; exact hs₁ g hg))
    (afp_comp π₂ (by rintro _ ⟨g, hg, rfl⟩; exact hs₂ g hg))
    (fun h hh => Submodule.mem_sup_right (mem_pFun.2 fun y => by
      simp only [h21]; exact addFun_zero hh.2))
    (fun h hh => Submodule.mem_sup_right (mem_pFun.2 fun y => by
      simp only [h12]; exact addFun_zero hh.2))
    (fun g hg => Submodule.mem_sup_right (mem_pFun.2 fun x => by
      have := hg.2 (ι₁ (π₁ x)) (ι₂ (π₂ x))
      rwa [hsum] at this))
  exact hasLen_equiv e (hasLen_prod hv ha hb)

theorem ret_om {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
    (hv : v.Integers R) {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (AA : HopfOrder (C := C) R N) {N₁ : Type} [AddCommGroup N₁] {N₂ : Type} [AddCommGroup N₂]
    (ι₁ : N₁ →+ N) (π₁ : N →+ N₁) (ι₂ : N₂ →+ N) (π₂ : N →+ N₂) (h11 : ∀ y, π₁ (ι₁ y) = y)
    (h22 : ∀ y, π₂ (ι₂ y) = y) (hsum : ∀ x, ι₁ (π₁ x) + ι₂ (π₂ x) = x) (h12 : ∀ y, π₁ (ι₂ y) = 0)
    (h21 : ∀ y, π₂ (ι₁ y) = 0) (hs₁ : ∀ g ∈ AA.carrier, (fun x => g (ι₁ (π₁ x))) ∈ AA.carrier)
    (hs₂ : ∀ g ∈ AA.carrier, (fun x => g (ι₂ (π₂ x))) ∈ AA.carrier) (a b : NNReal)
    (ha : HasLen v R (OmAA (AA.carrier.map (LinearMap.funLeft R C (ι₁ : N₁ → N)))) a)
    (hb : HasLen v R (OmAA (AA.carrier.map (LinearMap.funLeft R C (ι₂ : N₂ → N)))) b) :
    HasLen v R (OmAA AA.carrier) (a * b) := by
  have k₁ : ∀ h ∈ AA.carrier.map (LinearMap.funLeft R C (ι₁ : N₁ → N)),
      (fun x => h (π₁ x)) ∈ AA.carrier := by rintro _ ⟨g, hg, rfl⟩; exact hs₁ g hg
  have k₂ : ∀ h ∈ AA.carrier.map (LinearMap.funLeft R C (ι₂ : N₂ → N)),
      (fun x => h (π₂ x)) ∈ AA.carrier := by rintro _ ⟨g, hg, rfl⟩; exact hs₂ g hg
  obtain ⟨e⟩ := split_equiv ι₁ π₁ ι₂ π₂ (augIdeal AA.carrier) (sqIdeal (augIdeal AA.carrier))
    (augIdeal (AA.carrier.map (LinearMap.funLeft R C (ι₁ : N₁ → N))))
    (sqIdeal (augIdeal (AA.carrier.map (LinearMap.funLeft R C (ι₁ : N₁ → N)))))
    (augIdeal (AA.carrier.map (LinearMap.funLeft R C (ι₂ : N₂ → N))))
    (sqIdeal (augIdeal (AA.carrier.map (LinearMap.funLeft R C (ι₂ : N₂ → N))))) h11 h22
    (aug_comp ι₁ fun g hg => ⟨g, hg, rfl⟩) (aug_comp ι₂ fun g hg => ⟨g, hg, rfl⟩)
    (sq_comp ι₁ fun g hg => ⟨g, hg, rfl⟩) (sq_comp ι₂ fun g hg => ⟨g, hg, rfl⟩)
    (aug_comp π₁ k₁) (aug_comp π₂ k₂) (sq_comp π₁ k₁) (sq_comp π₂ k₂)
    (fun h hh => by
      simp only [h21, ((mem_aug _ _).1 hh).2]; exact Submodule.zero_mem _)
    (fun h hh => by
      simp only [h12, ((mem_aug _ _).1 hh).2]; exact Submodule.zero_mem _)
    (fun g hg => by
      have := aug_dec AA (ι₁.comp π₁) (ι₂.comp π₂) hs₁ hs₂ hg
      simpa only [AddMonoidHom.comp_apply, hsum] using this)
  exact hasLen_equiv e (hasLen_prod hv ha hb)

end PositivityTheory.HtPt.Re
