import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SpaceMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.AlgHomResUnique

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.Asm

section
variable {O Γ R R' : Type} [CommRing O] [Group Γ] [CommRing R] [CommRing R'] {Φ : Fr O Γ} {a : O →+* R} {P : PD Φ.ι Γ R}

theorem res_map' (h : Φ.Res a P) (f : R →+* R') : Φ.Res (f.comp a) (P.map f) := by
  have e : ∀ (S : Finset (ℤ × ℤ)) (X : M4 R), SuppM S X → SuppM S (X.map f) := fun S X hX i j h1 h2 => by
    rw [Matrix.map_apply, hX i j h1 h2, map_zero]
  refine ⟨fun g i => congrArg f (h.diag g i), fun v s hs i => ?_, ?_⟩
  · rw [PD.map_ψ, h.char v s hs i]; rfl
  · exact h.shape.imp (fun k => ⟨fun g => e _ _ (k.1 g), fun v => e _ _ (k.2 v)⟩) fun k g => e _ _ (k g)

theorem isRes_map [TopologicalSpace Γ] (h : Φ.IsRes a P) (f : R →+* R') : Φ.IsRes (f.comp a) (P.map f) :=
  ⟨h.pair.map f, res_map' h.res f, h.cont.map f bot_le⟩

theorem pair_of (f : R →+* R') (hf : Function.Injective f) (h : Φ.IsPair (f.comp a) (P.map f)) : Φ.IsPair a P := by
  have hi : ∀ X Y : M4 R, X.map f = Y.map f → X = Y := fun X Y e => Matrix.map_injective hf e
  have z : ∀ x, f x = 0 → x = 0 := fun x => (map_eq_zero_iff f hf).1
  have gs : ∀ (ν : R) (X : M4 R), IsGSp (f ν) (X.map f) → IsGSp ν X := fun ν X k => by
    unfold IsGSp at k ⊢
    apply hi
    rw [Matrix.map_mul, ← adj_map, k]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  refine ⟨fun g => gs _ _ (h.mult g), fun g hg => hi _ _ ?_, fun i j hij => z _ (h.nrm hij),
    fun v => ⟨gs _ _ (by rw [map_one]; exact (h.low v).1), fun i => hf ?_, fun i j hij => z _ ((h.low v).2.2 i j hij)⟩,
    fun v s hs i j hij => z _ ?_, fun v s hs i => hf ?_⟩
  · exact (h.kill g hg).trans (Matrix.map_one f (map_zero f) (map_one f)).symm
  · rw [map_one]; exact (h.low v).2.1 i
  · have k := h.flag v s hs i j hij
    rwa [PD.map_flag] at k
  · rw [map_one, ← PD.map_ψ]; exact h.mu v s hs i

theorem linked_self [TopologicalSpace Γ] (h : Φ.IsRes a P) : Φ.Linked a P P := by
  have e : ∀ t : R, (P.map C).map (evalRingHom t) = P := fun t => by
    have : (evalRingHom t).comp C = RingHom.id R := by ext; simp
    rw [PD.map_map, this]; rfl
  exact ⟨P.map C, isRes_map h C, e 0, e 1⟩

theorem linked_isRes [TopologicalSpace Γ] {P' : PD Φ.ι Γ R} (h : Φ.Linked a P P') : Φ.IsRes a P' := by
  obtain ⟨Q, hQ, -, rfl⟩ := h
  have k := isRes_map hQ (evalRingHom 1)
  have : (evalRingHom (1 : R)).comp (C.comp a) = a := by ext; simp
  rwa [this] at k

theorem chain_end [TopologicalSpace Γ] {P' : PD Φ.ι Γ R} (hP : Φ.IsRes a P) (h : Φ.Chain a P P') :
    Φ.IsRes a P' ∧ Φ.Good a P' := by
  obtain ⟨hg, hc⟩ := h
  induction hc with
  | refl => exact ⟨hP, hg⟩
  | tail _ hl _ => exact ⟨linked_isRes hl.2, hl.1⟩

end

section
variable {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ]
  {a : O →+* Λ} (X : Space Φ a) (J : Ideal X.B)

theorem end_pt {s t : PD Φ.ι Γ (ResidueField Λ)} (h : Φ.Linked ((residue Λ).comp a) s t) :
    ∃ x : X.A →ₐ[Λ] ResidueField Λ, X.P.map (x : X.A →+* ResidueField Λ) = t := by
  obtain ⟨Q, hQ, -, rfl⟩ := h
  obtain ⟨f, rfl, -⟩ := X.line Q hQ
  refine ⟨((aeval (1 : ResidueField Λ) : (ResidueField Λ)[X] →ₐ[ResidueField Λ] ResidueField Λ).restrictScalars Λ).comp f, ?_⟩
  rw [PD.map_map]
  congr 1

theorem someIn_of_locZero {K : Type} [CommRing K] [IsDomain K] (y : X.A →+* K) (h : X.LocZero J y) {p : Ideal X.A}
    (hp : RingHom.ker y ≤ p) : X.SomeIn J p := by
  haveI := RingHom.ker_isPrime y
  obtain ⟨q, hq, hle⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal X.A)) (J := RingHom.ker y) bot_le
  haveI : q.IsPrime := hq.1.1
  exact ⟨q, hq, hle.trans hp, Ideal.map_le_iff_le_comap.2 (h _ (Ideal.comap_isPrime _ q) fun s hs => hle hs)⟩

theorem zero_of_allIn {K : Type} [CommRing K] [IsDomain K] (y : X.A →+* K) {p : Ideal X.A} (h : X.AllIn J p)
    (hp : RingHom.ker y ≤ p) : ∀ b ∈ J, y (algebraMap X.B X.A b) = 0 := fun b hb => by
  haveI := RingHom.ker_isPrime y
  obtain ⟨q, hq, hle⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal X.A)) (J := RingHom.ker y) bot_le
  exact hle (h q hq (hle.trans hp) (Ideal.mem_map_of_mem _ hb))

end

theorem allIn_of_chain {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    [TotallyDisconnectedSpace Γ] {Φ : Fr O Γ} {l : ℕ} [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ]
    [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] {a : O →+* Λ} (hΦ : Φ.Std l a)
    (X : Space Φ a) (J : Ideal X.B)
    (hch : ∀ x : X.A →ₐ[Λ] ResidueField Λ, Φ.IsRes ((residue Λ).comp a) (X.P.map (x : X.A →+* ResidueField Λ)) →
      Φ.Good ((residue Λ).comp a) (X.P.map (x : X.A →+* ResidueField Λ)) → X.SomeIn J (RingHom.ker x) → X.AllIn J (RingHom.ker x))
    (x₀ x₁ : X.A →ₐ[Λ] ResidueField Λ) (hs : Φ.IsRes ((residue Λ).comp a) (X.P.map (x₀ : X.A →+* ResidueField Λ)))
    (hc : Φ.Chain ((residue Λ).comp a) (X.P.map (x₀ : X.A →+* ResidueField Λ)) (X.P.map (x₁ : X.A →+* ResidueField Λ)))
    (h₁ : X.SomeIn J (RingHom.ker x₁)) : X.AllIn J (RingHom.ker x₀) := by
  have key : ∀ s, Relation.ReflTransGen (fun x y => Φ.Good ((residue Λ).comp a) y ∧ Φ.Linked ((residue Λ).comp a) x y) s
      (X.P.map (x₁ : X.A →+* ResidueField Λ)) → Φ.IsRes ((residue Λ).comp a) s → Φ.Good ((residue Λ).comp a) s →
      ∀ x : X.A →ₐ[Λ] ResidueField Λ, X.P.map (x : X.A →+* ResidueField Λ) = s → X.AllIn J (RingHom.ker x) := by
    intro s h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro k1 k2 x e
      refine hch x (e ▸ k1) (e ▸ k2) ((conn Φ l a hΦ X J x x₁ ?_).2 (hch x₁ k1 k2 h₁))
      rw [e]
      exact linked_self k1
    | head hl _ ih =>
      rintro k1 k2 x rfl
      obtain ⟨x', rfl⟩ := end_pt X hl.2
      exact hch x k1 k2 ((conn Φ l a hΦ X J x x' hl.2).2 (ih (linked_isRes hl.2) hl.1 x' rfl))
  exact key _ hc.2 hs hc.1 x₀ rfl

end UpperTheory.V.Ws.Asm
