import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MemPowSmulLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IrrOfConn
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocFlat

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem cont_map {Γ R R' : Type} [TopologicalSpace Γ] [CommRing R] [CommRing R'] (f : R →+* R')
    {I : Ideal R} {J : Ideal R'} (h : I ≤ J.comap f) {a : Γ → R} (ha : AdicCont I a) :
    AdicCont J fun g => f (a g) := fun N =>
  (ha N).comp (Ideal.quotientMap _ f (le_trans (Ideal.pow_right_mono h N) (Ideal.le_comap_pow _ N)))

private theorem span_le_iff {G R R' : Type} {n : ℕ} [CommRing R] [CommRing R'] (f : R →+* R')
    (r : G → Fin n → Fin n → R) (p : Fin n → Fin n → Prop) (P : Ideal R') :
    Ideal.span {x | ∃ g i j, p i j ∧ x = f (r g i j)} ≤ P ↔
      Ideal.span {x | ∃ g i j, p i j ∧ x = r g i j} ≤ P.comap f := by
  rw [Ideal.span_le, Ideal.span_le]
  constructor
  · rintro h _ ⟨g, i, j, hp, rfl⟩
    exact h ⟨g, i, j, hp, rfl⟩
  · rintro h _ ⟨g, i, j, hp, rfl⟩
    exact h ⟨g, i, j, hp, rfl⟩

private theorem res_b {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    {F : Frame l (ResidueField O)} {n : ℕ} (S : Space O F n) (x : Ideal S.A) (L : S.Loc x) (hx : S.mB ≤ S.π x)
    (f : ResidueField O →+* ResidueField L.R) (hf : IsResMap O L.R f) (b : S.B) :
    residue L.R (L.ι (S.inc b)) = f (res O S.R b) := by
  obtain ⟨c, hc⟩ := residue_surjective (res O S.R (b : S.R))
  have h1 : b - algebraMap O S.B c ∈ S.mB := by
    show S.B.val (b - algebraMap O S.B c) ∈ maximalIdeal S.R
    rw [← res_eq_zero_iff O, map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, sub_eq_zero]
    exact hc.symm
  have h2 : S.inc (b - algebraMap O S.B c) ∈ x := hx h1
  rw [← L.lies] at h2
  have h3 : L.ι (S.inc (b - algebraMap O S.B c)) ∈ maximalIdeal L.R := h2
  rw [map_sub, map_sub, AlgHom.commutes, AlgHom.commutes] at h3
  rw [← hc, hf c]
  exact Ideal.Quotient.eq.2 h3

theorem UpperTheory.V.Fr.loc_rho :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), L.ρ.Cont (maximalIdeal L.R) ∧ (∀ f, IsResMap O L.R f → (L.ρ.map (residue L.R)).IsBar f) ∧ (∀ P : Ideal L.R, (L.ρ.triP ≤ P ↔ S.u.triP ≤ L.im P) ∧ (L.ρ.triM ≤ P ↔ S.u.triM ≤ L.im P) ∧ (L.ρ.ee ≤ P ↔ S.u.ee ≤ L.im P)) ∧ (¬ S.u.triP ≤ x → L.ρ.triP = ⊤ ∧ L.ρ.triM ≤ maximalIdeal L.R) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x L
  obtain ⟨-, -, hx⟩ := UpperTheory.V.Fr.loc_flat hF hn S x L
  obtain ⟨⟨hc1, hc2⟩, -⟩ := UpperTheory.V.Fr.cont_u hF hn S
  have hx0 : S.x0 ≤ (maximalIdeal L.R).comap (L.ι : S.A →+* L.R) := by
    rw [L.lies]
    exact Ideal.map_le_iff_le_comap.2 hx
  have h3 : ∀ P : Ideal L.R, (L.ρ.triP ≤ P ↔ S.u.triP ≤ L.im P) ∧ (L.ρ.triM ≤ P ↔ S.u.triM ≤ L.im P) ∧
      (L.ρ.ee ≤ P ↔ S.u.ee ≤ L.im P) := fun P =>
    ⟨span_le_iff (L.ι : S.A →+* L.R) (fun g i j => S.u.r g i j) (fun i j => j < i) P,
      span_le_iff (L.ι : S.A →+* L.R) (fun g i j => S.u.r g i j) (fun i j => i < j) P,
      span_le_iff (L.ι : S.A →+* L.R) (fun g i j => S.u.r g i j) (fun i j => Odd (w n i - w n j)) P⟩
  have him : L.im (maximalIdeal L.R) = x := L.lies
  refine ⟨⟨fun i j => cont_map _ hx0 (hc1 i j), fun v i => cont_map _ hx0 (hc2 v i)⟩,
    fun f hf => ⟨fun g i => ?_, fun v i g => ?_⟩, h3, fun hP => ⟨?_, ?_⟩⟩
  · exact (res_b S x L hx f hf (S.aB g i)).trans (congrArg f (S.lift.2.1.1 g i))
  · exact (res_b S x L hx f hf (S.ψB v i g)).trans (congrArg f (S.lift.2.1.2 v i g))
  · by_contra hne
    exact hP (him ▸ (h3 _).1.1 (IsLocalRing.le_maximalIdeal hne))
  · have hk : RingHom.ker ((residue L.R).comp (L.ι : S.A →+* L.R)) = x := by
      rw [← RingHom.comap_ker, IsLocalRing.ker_residue]
      exact L.lies
    have := (UpperTheory.V.Fr.types hF hn S (ResidueField L.R) ((residue L.R).comp (L.ι : S.A →+* L.R))).2
    rw [hk] at this
    rw [(h3 _).2.1, him]
    exact (this hx).resolve_left hP
