import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormaliserUnipSymCharPatternStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsScalarMulIntegralOfNormalizesSymmetricLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsScalarMulIntegralOfConjIntegralGeneratorsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdjoinRangeGLEqTopMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdjoinUnitaryGroupHermitianLocalEqTopStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryScalarMulIntegralLocalToGlobalStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryIntegralOfSplitPlaceComponentStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormOneWithResiduesAtSplitPlacesStatement

noncomputable section

open Matrix Formalism.UG Formalism.L2.DIV

namespace GlobalTheory.LevNorm

theorem bc_bc {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {n : ℕ} (f : R →+* R') (g : R' →+* R'')
    (x : GL (Fin n) R) : bc g (bc f x) = bc (g.comp f) x := Units.ext rfl

theorem bc_injective {R R' : Type} [CommRing R] [CommRing R'] {n : ℕ} {f : R →+* R'} (hf : Function.Injective f) :
    Function.Injective (bc (n := Fin n) f) := fun _ _ h =>
  Units.ext (Matrix.map_injective hf (congrArg Units.val h))

theorem bc_surjective {R k : Type} [CommRing R] [IsLocalRing R] [Field k] {n : ℕ} {f : R →+* k} (hf : Function.Surjective f) :
    Function.Surjective (bc (n := Fin n) f) := fun y => by
  choose j hj using hf
  have e : f.mapMatrix ((y : Matrix (Fin n) (Fin n) k).map j) = y := by ext a b; exact hj _
  haveI : IsLocalHom f := IsLocalHom.of_surjective f fun a => ⟨j a, hj a⟩
  have hu : IsUnit ((y : Matrix (Fin n) (Fin n) k).map j) := by
    rw [Matrix.isUnit_iff_isUnit_det, ← isUnit_map_iff f, RingHom.map_det, e, ← Matrix.isUnit_iff_isUnit_det]
    exact y.isUnit
  exact ⟨hu.unit, Units.ext e⟩

variable {A : Type} [CommRing A] {S : Subring A} {P : Type} {k : P → Type} [∀ Q, Field (k Q)] (r : ∀ Q, S →+* k Q)
  (σ : A →+* A) {n : ℕ} (ρ κ : ℕ) (G : GL (Fin n) S) (T : Finset P) (ψ : ∀ Q, AddChar (k Q) ℂ) (a : ∀ Q, Fin n → Fin n → k Q)

def InLev (x : GL (Fin n) S) : Prop :=
  bc S.subtype x ∈ UJ σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) ∧ ∀ Q ∈ T, bc (r Q) x ∈ unipSym (k Q) n ρ κ

def levChr (x : GL (Fin n) S) : ℂ := ∏ Q ∈ T, ψ Q (edgeVal ρ κ (a Q) (bc (r Q) x))

def Keeps (m : GL (Fin n) A) : Prop :=
  ∀ x, InLev r σ ρ κ G T x → ∃ x', bc S.subtype x' = m * bc S.subtype x * m⁻¹ ∧ InLev r σ ρ κ G T x' ∧
    levChr r ρ κ T ψ a x' = levChr r ρ κ T ψ a x

variable {r σ ρ κ G T ψ a} (Z : PlaceSys A S P k r)

theorem bc_pO (Q : P) (x : GL (Fin n) S) : bc (Z.O Q).subtype (bc (Z.pO Q) x) = bc (Z.p Q) (bc S.subtype x) := Units.ext rfl

theorem bc_res {Q : P} {f : Z.O Q →+* k Q} (hf : ∀ s, f (Z.pO Q s) = r Q s) (x : GL (Fin n) S) :
    bc f (bc (Z.pO Q) x) = bc (r Q) x := by
  rw [bc_bc, show f.comp (Z.pO Q) = r Q from RingHom.ext hf]

theorem bc_r_one {Q : P} {x : GL (Fin n) S} (h : bc (Z.pO Q) x = 1) : bc (r Q) x = 1 := by
  obtain ⟨f, -, hf⟩ := Z.exists_res Q
  rw [← bc_res Z hf, h, map_one]

theorem pO_conj_one {Q : P} {m : GL (Fin n) A} {x x' : GL (Fin n) S} (e : bc S.subtype x' = m * bc S.subtype x * m⁻¹)
    (h : bc (Z.pO Q) x = 1) : bc (Z.pO Q) x' = 1 := by
  apply bc_injective (Z.O Q).subtype_injective
  rw [bc_pO, e, map_mul, map_mul, ← bc_pO, h, map_one, mul_one, ← map_mul, mul_inv_cancel, map_one]

theorem loc_split (hσ : ∀ a, σ (σ a) = a) (hS : ∀ a ∈ S, σ a ∈ S)
    (hG : cT σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A))
    {Q Q' : P} (h : σ (Z.e Q) = Z.e Q') (hne : Q ≠ Q') (hQ' : Q' ∉ T) {f : Z.O Q →+* k Q} (hf : ∀ s, f (Z.pO Q s) = r Q s)
    {m : GL (Fin n) A} (hm : Keeps r σ ρ κ G T ψ a m) (y : GL (Fin n) (Z.O Q)) (hy : Q ∈ T → bc f y ∈ unipSym (k Q) n ρ κ) :
    ∃ y' : GL (Fin n) (Z.O Q), bc (Z.O Q).subtype y' = bc (Z.p Q) m * bc (Z.O Q).subtype y * (bc (Z.p Q) m)⁻¹ ∧
      (Q ∈ T → bc f y' ∈ unipSym (k Q) n ρ κ ∧ ψ Q (edgeVal ρ κ (a Q) (bc f y')) = ψ Q (edgeVal ρ κ (a Q) (bc f y))) := by
  obtain ⟨u, hu, rfl, h1⟩ := GlobalTheory.T.exists_unitary_integral_of_splitPlace_component Z σ hσ hS n G hG Q Q' h hne y
  have h2 : ∀ Q'' ∈ T, Q'' ≠ Q → bc (Z.pO Q'') u = 1 := fun Q'' hT e => h1 Q'' e fun e' => hQ' (e' ▸ hT)
  obtain ⟨x', e, hx', hc⟩ := hm u ⟨hu, fun Q'' hT => by
    by_cases e : Q'' = Q
    · subst e; rw [← bc_res Z hf]; exact hy hT
    · rw [bc_r_one Z (h2 _ hT e)]; exact one_mem _⟩
  refine ⟨bc (Z.pO Q) x', by rw [bc_pO, bc_pO, e, map_mul, map_mul, map_inv], fun hT => ?_⟩
  rw [bc_res Z hf, bc_res Z hf]
  refine ⟨hx'.2 Q hT, ?_⟩
  unfold levChr at hc
  rwa [Finset.prod_eq_single_of_mem Q hT, Finset.prod_eq_single_of_mem Q hT] at hc
  · intro Q'' hT' e'
    rw [bc_r_one Z (h2 _ hT' e'), edgeVal_one, AddChar.map_zero_eq_one]
  · intro Q'' hT' e'
    rw [bc_r_one Z (pO_conj_one Z e (h2 _ hT' e')), edgeVal_one, AddChar.map_zero_eq_one]

theorem map_cT {Q Q' : P} {s : Z.K Q →+* Z.K Q'} (hs : ∀ a, s (Z.p Q a) = Z.p Q' (σ a)) (M : Matrix (Fin n) (Fin n) A) :
    (Z.p Q').mapMatrix (cT σ M) = (((Z.p Q).mapMatrix M).map s)ᵀ := by
  ext i j
  exact (hs _).symm

theorem loc_inert (hσ : ∀ a, σ (σ a) = a) (hS : ∀ a ∈ S, σ a ∈ S) (hn : 3 ≤ n)
    (hG : cT σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A))
    {Q : P} (h : σ (Z.e Q) = Z.e Q) (hQ : Q ∉ T) (δ : S) (hδ : r Q (δ - ⟨σ δ, hS _ δ.2⟩) ≠ 0)
    {m : GL (Fin n) A} (hm : Keeps r σ ρ κ G T ψ a m) : IsScal (Z.O Q) (bc (Z.p Q) m) := by
  obtain ⟨s, hs, hsO⟩ := Z.exists_conj hS h
  obtain ⟨f, hf0, hf⟩ := Z.exists_res Q
  let t : Z.O Q →+* Z.O Q := (s.comp (Z.O Q).subtype).codRestrict (Z.O Q) fun x => hsO _ x.2
  have ht : ∀ x : S, t (Z.pO Q x) = Z.pO Q ⟨σ x, hS _ x.2⟩ := fun x => Subtype.ext (hs _)
  have htt : ∀ x, t (t x) = x := fun x => by
    obtain ⟨x, rfl⟩ := Z.pO_surj Q x
    rw [ht, ht]
    exact congrArg _ (Subtype.ext (hσ _))
  haveI : IsLocalHom f := IsLocalHom.of_surjective f hf0
  have hδ' : IsUnit (Z.pO Q δ - t (Z.pO Q δ)) := by
    rw [ht, ← map_sub, ← isUnit_map_iff f, hf]
    exact hδ.isUnit
  have inj : Function.Injective fun M : Matrix (Fin n) (Fin n) (Z.O Q) => M.map (Z.O Q).subtype :=
    Matrix.map_injective (Z.O Q).subtype_injective
  have hgen := GlobalTheory.T.adjoin_unitaryGroup_hermitian_local_eq_top (Z.O Q) t htt ⟨_, hδ'⟩ n hn ((bc (Z.pO Q) G : GL (Fin n) (Z.O Q)) : Matrix (Fin n) (Fin n) (Z.O Q))
    (inj ((map_cT Z hs _).symm.trans (congrArg (Z.p Q).mapMatrix hG))) (Units.isUnit _)
  refine GlobalTheory.T.isScalarMulIntegral_of_conj_integral_generators _ _ n _ _ hgen fun y hy => ?_
  obtain ⟨x, hx1, hx2⟩ := Z.gl_single Q (bc (Z.O Q).subtype y)
  obtain ⟨u, rfl⟩ := Z.gl_int (x := x) fun Q' => by
    by_cases e : Q' = Q
    · subst e; exact ⟨y, hx1.symm⟩
    · exact ⟨1, by rw [hx2 _ e, map_one]⟩
  have hu1 : bc (Z.pO Q) u = y := bc_injective (Z.O Q).subtype_injective hx1
  have hu2 : ∀ Q', Q' ≠ Q → bc (Z.pO Q') u = 1 := fun Q' e =>
    bc_injective (Z.O Q').subtype_injective (by rw [bc_pO, hx2 _ e, map_one])
  have hU : bc S.subtype u ∈ UJ σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) := by
    refine Matrix.ext fun i j => Z.ext' fun Q' => ?_
    refine congrFun (congrFun (show (Z.p Q').mapMatrix _ = (Z.p Q').mapMatrix _ from ?_) i) j
    rw [map_mul, map_mul]
    by_cases e : Q' = Q
    · subst e
      rw [map_cT Z hs]
      have h3 : (Z.p Q').mapMatrix ((bc S.subtype u : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) =
        (Z.O Q').subtype.mapMatrix (y : Matrix (Fin n) (Fin n) (Z.O Q')) := congrArg Units.val hx1
      have h4 := congrArg (Z.O Q').subtype.mapMatrix (show cT t _ * _ * _ = _ from hy)
      rw [map_mul, map_mul] at h4
      rw [h3]
      exact h4
    · obtain ⟨Q₁, h1⟩ := Z.exists_bar hσ Q'
      have h1' : σ (Z.e Q₁) = Z.e Q' := by rw [← h1, hσ]
      obtain ⟨s', hs', -⟩ := Z.exists_conj hS h1'
      have e1 : Q₁ ≠ Q := fun e' => e (Z.e_injective (by rw [← h1', e', h]))
      have h3 : ∀ Q'', Q'' ≠ Q → (Z.p Q'').mapMatrix ((bc S.subtype u : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = 1 :=
        fun Q'' e' => congrArg Units.val (hx2 Q'' e')
      rw [map_cT Z hs', h3 _ e, h3 _ e1, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, one_mul, mul_one]
  obtain ⟨x', e, -, -⟩ := hm u ⟨hU, fun Q' hT => by
    rw [bc_r_one Z (hu2 _ fun e => hQ (e ▸ hT))]; exact one_mem _⟩
  exact ⟨bc (Z.pO Q) x', by rw [bc_pO, ← hu1, bc_pO, e, map_mul, map_mul, map_inv]⟩

theorem conj_of_smul {R : Type} [CommRing R] {z z' : R} (hz : z * z' = 1) {m x : GL (Fin n) R}
    (h : (m : Matrix (Fin n) (Fin n) R) = z • (x : Matrix (Fin n) (Fin n) R)) (y : GL (Fin n) R) :
    m * y * m⁻¹ = x * y * x⁻¹ ∧ m⁻¹ * y * m = x⁻¹ * y * x := by
  have h1 : ∀ y : GL (Fin n) R, (m * x⁻¹) * y = y * (m * x⁻¹) := fun y => Units.ext (by
    simp only [Units.val_mul, h, Matrix.smul_mul, Matrix.mul_smul, Units.mul_inv, Matrix.one_mul, Matrix.mul_one])
  obtain ⟨w, rfl⟩ : ∃ w, m = w * x := ⟨m * x⁻¹, by group⟩
  rw [mul_inv_cancel_right] at h1
  constructor
  · calc _ = w * (x * y * x⁻¹) * w⁻¹ := by group
      _ = _ := by rw [h1]; group
  · calc _ = x⁻¹ * (w⁻¹ * (y * w)) * x := by group
      _ = _ := by rw [← h1]; group

theorem normaliser_core (hσ : ∀ a, σ (σ a) = a) (hS : ∀ a ∈ S, σ a ∈ S) (hn : n = 2 * ρ + κ + 1) (hρ : 1 ≤ ρ) (hκ : 2 ≤ κ)
    (hG : cT σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A))
    (hT : ∀ Q ∈ T, ∀ Q' ∈ T, σ (Z.e Q) ≠ Z.e Q')
    (hun : ∀ Q, σ (Z.e Q) = Z.e Q → ∃ δ : S, r Q (δ - ⟨σ δ, hS _ δ.2⟩) ≠ 0)
    (hψ : ∀ Q ∈ T, ψ Q ≠ 1) (ha : ∀ Q ∈ T, ∀ i j, symEdge ρ κ i j → a Q i j ≠ 0)
    {m : GL (Fin n) A} (hU : m ∈ UJ σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A))
    (hm : Keeps r σ ρ κ G T ψ a m) (hm' : Keeps r σ ρ κ G T ψ a m⁻¹) :
    ∃ (z : A) (c : S) (x : GL (Fin n) S), z * σ z = 1 ∧ (c : A) * σ c = 1 ∧
      (∀ b : A, (∀ Q ∈ T, Z.p Q b ∈ Z.O Q ∧ Z.p Q (σ b) ∈ Z.O Q) → (1 - (c : A)) * b ∈ S) ∧
      (m : Matrix (Fin n) (Fin n) A) = z • ((bc S.subtype x : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) ∧
      ∀ Q ∈ T, ∃ h ∈ unipSym (k Q) n ρ κ,
        ((bc (r Q) x : GL (Fin n) (k Q)) : Matrix (Fin n) (Fin n) (k Q)) = midDiag n ρ κ 1 (r Q c) * (h : Matrix (Fin n) (Fin n) (k Q)) := by
  classical
  choose bar hbar using Z.exists_bar hσ
  choose f hf0 hf using Z.exists_res
  have hb1 : ∀ Q ∈ T, Q ≠ bar Q := fun Q hQ e => hT Q hQ Q hQ (by rw [hbar, ← e])
  have hb2 : ∀ Q ∈ T, bar Q ∉ T := fun Q hQ e => hT Q hQ _ e (hbar Q)
  have hscT : ∀ Q ∈ T, IsScal (Z.O Q) (bc (Z.p Q) m) := fun Q hQ =>
    GlobalTheory.T.isScalarMul_integral_of_normalizes_symmetricLevel _ _ _ (f Q) (hf0 Q) n ρ κ hn hρ (ψ Q) (hψ Q hQ) (a Q) (ha Q hQ) _
      (fun y hy => by
        obtain ⟨y', h1, h2⟩ := loc_split Z hσ hS hG (hbar Q) (hb1 Q hQ) (hb2 Q hQ) (hf Q) hm y fun _ => hy
        exact ⟨y', h1, (h2 hQ).2⟩)
      (fun y hy => by
        obtain ⟨y', h1, -⟩ := loc_split Z hσ hS hG (hbar Q) (hb1 Q hQ) (hb2 Q hQ) (hf Q) hm' y fun _ => hy
        exact ⟨y', by rwa [map_inv, inv_inv] at h1⟩)
  obtain ⟨z₁, x₁, hz₁, hx₁⟩ := GlobalTheory.T.unitary_scalarMulIntegral_local_to_global Z σ hσ hS n G m hU fun Q => by
    by_cases hQ : Q ∈ T
    · exact Or.inl (hscT Q hQ)
    by_cases hQ' : bar Q ∈ T
    · exact Or.inr ⟨bar Q, by rw [← hbar, hσ], hscT _ hQ'⟩
    left
    by_cases e : Q = bar Q
    · have h1 : σ (Z.e Q) = Z.e Q := by rw [hbar, ← e]
      obtain ⟨δ, hδ⟩ := hun Q h1
      exact loc_inert Z hσ hS (by omega) hG h1 hQ δ hδ hm
    · refine GlobalTheory.T.isScalarMulIntegral_of_conj_integral_generators _ _ n _ _ (GlobalTheory.T.adjoin_range_GL_eq_top_matrix _ n) fun y _ => ?_
      obtain ⟨y', h1, -⟩ := loc_split Z hσ hS hG (hbar Q) e hQ' (hf Q) hm y fun h => absurd h hQ
      exact ⟨y', h1⟩
  have red : ∀ x : GL (Fin n) S, Keeps r σ ρ κ G T ψ a (bc S.subtype x) → ∀ Q ∈ T, ∀ h ∈ unipSym (k Q) n ρ κ,
      bc (r Q) x * h * (bc (r Q) x)⁻¹ ∈ unipSym (k Q) n ρ κ ∧
        ψ Q (edgeVal ρ κ (a Q) (bc (r Q) x * h * (bc (r Q) x)⁻¹)) = ψ Q (edgeVal ρ κ (a Q) h) := by
    intro x hx Q hQ h hh
    obtain ⟨y, rfl⟩ := bc_surjective (hf0 Q) h
    obtain ⟨y', h1, h2⟩ := loc_split Z hσ hS hG (hbar Q) (hb1 Q hQ) (hb2 Q hQ) (hf Q) hx y fun _ => hh
    have h3 : y' = bc (Z.pO Q) x * y * (bc (Z.pO Q) x)⁻¹ :=
      bc_injective (Z.O Q).subtype_injective (by rw [h1, map_mul, map_mul, map_inv, bc_pO])
    have h4 := h2 hQ
    rwa [h3, map_mul, map_mul, map_inv, bc_res Z (hf Q)] at h4
  have k1 : Keeps r σ ρ κ G T ψ a (bc S.subtype x₁) := fun x hx => by
    obtain ⟨x', h1, h2⟩ := hm x hx
    exact ⟨x', by rw [h1, (conj_of_smul hz₁ hx₁ _).1], h2⟩
  have k2 : Keeps r σ ρ κ G T ψ a (bc S.subtype x₁⁻¹) := fun x hx => by
    obtain ⟨x', h1, h2⟩ := hm' x hx
    exact ⟨x', by rw [h1, map_inv, inv_inv, inv_inv, (conj_of_smul hz₁ hx₁ _).2], h2⟩
  have fin : ∀ Q, ∃ s c : (k Q)ˣ, Q ∈ T → ∃ h ∈ unipSym (k Q) n ρ κ,
      ((bc (r Q) x₁ : GL (Fin n) (k Q)) : Matrix (Fin n) (Fin n) (k Q)) =
        midDiag n ρ κ (s : k Q) (c : k Q) * (h : Matrix (Fin n) (Fin n) (k Q)) := fun Q => by
    by_cases hQ : Q ∈ T
    · obtain ⟨s, c, h⟩ := GlobalTheory.T.normaliser_unipSym_char_pattern (k Q) n ρ κ hn hρ hκ (ψ Q) (hψ Q hQ) (a Q) (ha Q hQ) _ (red x₁ k1 Q hQ) fun h hh => by
        have := (red _ k2 Q hQ h hh).1
        rwa [map_inv, inv_inv] at this
      exact ⟨s, c, fun _ => h⟩
    · exact ⟨1, 1, fun h => absurd h hQ⟩
  choose s c hsc using fin
  obtain ⟨z₂, hz₂, hr₂, -⟩ := GlobalTheory.T.exists_normOne_with_residues_at_splitPlaces Z σ hσ hS T hT s
  obtain ⟨c', hc', hrc, hsup⟩ := GlobalTheory.T.exists_normOne_with_residues_at_splitPlaces Z σ hσ hS T hT fun Q => (s Q)⁻¹ * c Q
  let w : S := ⟨σ z₂, hS _ z₂.2⟩
  have hw : z₂ * w = 1 := Subtype.ext hz₂
  have hw' : w * z₂ = 1 := by rw [mul_comm, hw]
  refine ⟨z₁ * z₂, c', ⟨w • x₁.1, z₂ • (x₁⁻¹).1, ?_, ?_⟩, ?_, hc', hsup, ?_, fun Q hQ => ?_⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hw', Units.mul_inv, one_smul]
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hw, Units.inv_mul, one_smul]
  · rw [map_mul, mul_mul_mul_comm, hz₁, hz₂, one_mul]
  · rw [hx₁]
    ext i j
    show z₁ * _ = z₁ * z₂ * (σ z₂ * (x₁.1 i j : A))
    rw [mul_assoc, ← mul_assoc (z₂ : A), hz₂, one_mul]
    rfl
  · obtain ⟨h, hh, e⟩ := hsc Q hQ
    refine ⟨h, hh, ?_⟩
    have h1 : r Q w = ((s Q)⁻¹ : (k Q)ˣ) := by
      have := congrArg (r Q) hw
      rw [map_mul, map_one, hr₂ Q hQ] at this
      exact (Units.inv_eq_of_mul_eq_one_right this).symm
    ext i j
    have e' := congrFun (congrFun e i) j
    show r Q (w * x₁.1 i j) = _
    rw [map_mul, show r Q (x₁.1 i j) = _ from e', h1, hrc Q hQ]
    simp only [midDiag, Matrix.diagonal_mul]
    split_ifs
    · rw [Units.val_mul, mul_assoc]
    · rw [← mul_assoc, Units.inv_mul]

end GlobalTheory.LevNorm

end
