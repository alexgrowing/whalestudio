import Development.WeilBound.CoreStatements.AutomorphicKernels.DeRhamPotentiallySemistable.DeRhamTwists.ContinuousCyclotomicCharacter
import GroundTheory.PAdicHodge.WAKummer
import GroundTheory.PAdicHodge.FundamentalSeq
import GroundTheory.PAdicHodge.SenTateCharClosure

noncomputable section

namespace period_ring_base

open Formalism.Per6 hiding σB aB
open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst PfDRPst Matrix

variable (l : ℕ) [Fact l.Prime]

abbrev GQ : Type := PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l

abbrev Fld : Type := IntermediateField ℚ_[l] (PadicAlgCl l)

abbrev B : Type := Bcris l

def φ : B l →+* B l := φB l

theorem isUnit_iC_l : IsUnit (iC l (l : ACris.ACris ℂ_[l] l)) := by
  rw [map_natCast, ← map_natCast (qQ l)]
  exact (IsUnit.mk0 (l : ℚ_[l]) (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)).map _

theorem isUnit_image_period : IsUnit (iC l (tA l)) := IsUnit.mk0 _ DeRhamTwist.Twist.tQ_ne

def ι : B l →+* BdR l := Loc2.lift (iC l) (isUnit_iC_l l) (isUnit_image_period l)

def iA (a : ℕ) : B l →+* BdR l := (ι l).comp (φ l ^ a)

theorem isUnit_l : IsUnit (l : B l) := by
  rw [← map_natCast (cB l)]
  exact Loc2.isUnit_left _ _

theorem isUnit_zB (z : nonZeroDivisors ℤ_[l]) : IsUnit (zB l z) := by
  have hz : (z : ℤ_[l]) ≠ 0 := nonZeroDivisors.coe_ne_zero z
  rw [PadicInt.unitCoeff_spec hz, map_mul, map_pow, map_natCast]
  exact ((PadicInt.unitCoeff hz).isUnit.map _).mul ((isUnit_l l).pow _)

def qB : ℚ_[l] →+* B l := IsLocalization.lift (M := nonZeroDivisors ℤ_[l]) (isUnit_zB l)

def t : B l := cB l (tA l)

def aB : AInf ℂ_[l] l →+* B l := (cB l).comp (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l))

def Ainf' : Subring (B l) := Subring.closure (Set.range (aB l) ∪ {qB l ((l : ℚ_[l])⁻¹)})

def Plus : Subring (BdR l) := (algebraMap (BdRp l) (BdR l)).range

open Classical in

def th (x : BdR l) : ℂ_[l] := if h : x ∈ Plus l then θD l (RingHom.mem_range.1 h).choose else 0

variable {l}

def σB (g : GQ l) : B l →+* B l := Formalism.Per6.σB g

def σC (g : GQ l) : ℂ_[l] ≃+* ℂ_[l] := galCp (toBot g)

def χ (g : GQ l) : ℚ_[l] := ((DeRhamTwist.Twist.chi0 l g : ℤ_[l]) : ℚ_[l])

def κ (g : GQ l) : ℚ_[l] :=
  (kummerC (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one (toBot g) : ℤ_[l])

def Ine (g : GQ l) : Prop := ∀ y : PadicAlgCl l, ‖y‖ ≤ 1 → ‖g y - y‖ < 1

def Eig (h : ℕ) (m : ℤ) (x : B l) : Prop := (φ l ^ h) x = qB l ((l : ℚ_[l]) ^ m) * x

def IntAll (x : B l) : Prop := ∀ a, iA l a x ∈ Plus l

def InE (h : ℕ) (x : B l) : Prop := Eig h 0 x ∧ IntAll x

def FixE (h : ℕ) (L : Fld l) : Prop := ∀ σ ∈ L.fixingSubgroup, ∀ x : B l, InE h x → σB σ x = x

structure Unr (h : ℕ) (L : Fld l) {n : Type} [Fintype n] [DecidableEq n]
    (δ : L.fixingSubgroup → Matrix n n (B l)) (U U' : Matrix n n (B l)) : Prop where
  inE : ∀ σ i j, InE h (δ σ i j)
  mem : ∀ i j, U i j ∈ Ainf' l ∧ U' i j ∈ Ainf' l
  inv : U * U' = 1
  triv : ∀ σ : L.fixingSubgroup, δ σ * U.map (σB σ.1) = U

structure Base (l : ℕ) [Fact l.Prime] : Prop where
  dom : IsDomain (B l)
  ι_inj : Function.Injective (ι l)
  σ_one : σB (1 : GQ l) = RingHom.id _
  σ_mul : ∀ g h : GQ l, σB (g * h) = (σB g).comp (σB h)
  σD_one : ∀ x, σD (1 : GQ l) x = x
  σD_mul : ∀ (g h : GQ l) x, σD (g * h) x = σD g (σD h x)
  σC_one : ∀ x, σC (1 : GQ l) x = x
  σC_mul : ∀ (g h : GQ l) x, σC (g * h) x = σC g (σC h x)
  φ_σ : ∀ (g : GQ l) x, φ l (σB g x) = σB g (φ l x)
  ι_σ : ∀ (g : GQ l) x, ι l (σB g x) = σD g (ι l x)
  φ_q : ∀ q, φ l (qB l q) = qB l q
  σ_q : ∀ (g : GQ l) q, σB g (qB l q) = qB l q
  ι_q : ∀ q, ι l (qB l q) = qQ l q
  ι_t : ι l (t l) = tQ l
  t_unit : IsUnit (t l)
  frobenius_period : φ l (t l) = (l : B l) * t l
  galois_t_transform : ∀ g : GQ l, σB g (t l) = qB l (χ g) * t l
  σ_u : ∀ g : GQ l, σD g (uQ l) = uQ l + qQ l (κ g) * tQ l
  κ_mul : ∀ g h : GQ l, κ (g * h) = κ g + χ g * κ h
  κ_cont : Continuous (κ : GQ l → ℚ_[l])
  χ_cont : Continuous (χ : GQ l → ℚ_[l])
  ι_Bst : ∀ x, ι l x ∈ Bst l
  u_Bst : uQ l ∈ Bst l
  plus_σ : ∀ (g : GQ l) x, x ∈ Plus l → σD g x ∈ Plus l
  th_σ : ∀ (g : GQ l) x, x ∈ Plus l → th l (σD g x) = σC g (th l x)
  th_add : ∀ x ∈ Plus l, ∀ y ∈ Plus l, th l (x + y) = th l x + th l y
  th_mul : ∀ x ∈ Plus l, ∀ y ∈ Plus l, th l (x * y) = th l x * th l y
  th_q : ∀ q, qQ l q ∈ Plus l ∧ th l (qQ l q) = algebraMap ℚ_[l] ℂ_[l] q
  th_zero : ∀ x ∈ Plus l, (th l x = 0 ↔ ∃ y ∈ Plus l, x = tQ l * y)
  t_plus : tQ l ∈ Plus l
  val : ∀ x : BdR l, x ≠ 0 → ∃ (i : ℤ) (u v : BdR l), u ∈ Plus l ∧ v ∈ Plus l ∧ u * v = 1 ∧ x = tQ l ^ i * u
  orbit : ∀ x : ℂ_[l], Continuous fun g : GQ l => σC g x
  fs_ker : ∀ x, φ l x = x → ι l x ∈ Plus l → ∃ q, x = qB l q
  fs_surj : ∀ z : BdR l, ∃ x, φ l x = x ∧ ι l x - z ∈ Plus l
  ainf_φ : ∀ x ∈ Ainf' l, φ l x ∈ Ainf' l
  ainf_σ : ∀ (g : GQ l), ∀ x ∈ Ainf' l, σB g x ∈ Ainf' l
  ainf_plus : ∀ x ∈ Ainf' l, ι l x ∈ Plus l
  ainf_eig : ∀ (h : ℕ) (m : ℤ), m ≠ 0 → ∀ x ∈ Ainf' l, Eig h m x → x = 0
  fixed : ∀ L : Fld l, FiniteDimensional ℚ_[l] L → ∃ (f : ℕ) (b : Fin f → B l),
    (∀ i, b i ∈ Ainf' l ∧ ∀ σ ∈ L.fixingSubgroup, σB σ (b i) = b i) ∧
    ∀ x, (∀ σ ∈ L.fixingSubgroup, σB σ x = x) → ∃ q : Fin f → ℚ_[l], x = ∑ i, qB l (q i) * b i
  no_kummer : ∀ L : Fld l, FiniteDimensional ℚ_[l] L → ∀ x : B l,
    ¬ ∀ σ ∈ L.fixingSubgroup, σB σ x - x = qB l (κ σ) * t l

def PeriodRingBase : Prop := ∀ (l : ℕ) [Fact l.Prime], Base l

def DieudonneManinBasisModification : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (d : ℕ) (P Q : Matrix (Fin d) (Fin d) (BdR l)), (∀ i j, P i j ∈ Plus l) → P * Q = 1 →
    ∃ (h : ℕ) (c : Fin d → ℤ) (e : ℕ) (W W' : Matrix (Fin d) (Fin d) (B l)), 0 < h ∧
      W * W' = (t l ^ e) • (1 : Matrix (Fin d) (Fin d) (B l)) ∧ (∀ i j, Eig h (c j) (W i j)) ∧
      ∀ a, ∃ Pa Qa : Matrix (Fin d) (Fin d) (BdR l), (∀ i j, Pa i j ∈ Plus l ∧ Qa i j ∈ Plus l) ∧ Pa * Qa = 1 ∧
        W.map (iA l a) * Pa = P

def NegativeSlopeIntegralVanishes : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (m : ℤ) (x : B l), 0 < h → m < 0 → Eig h m x → IntAll x → x = 0

def UnramifiedExtensionDegree : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (h : ℕ), 0 < h →
    (∃ K₀ : Fld l, FiniteDimensional ℚ_[l] K₀ ∧ FixE h K₀) ∧
    (∀ x : B l, InE h x → x ∈ Ainf' l ∧ (x ≠ 0 → ∃ y, InE h y ∧ x * y = 1)) ∧
    ∃ (e : Fin h → B l) (M : Matrix (Fin h) (Fin h) (B l)), (∀ b, InE h (e b) ∧ e b ∈ Set.range (aB l)) ∧
      (∀ x : B l, InE h x → ∃ q : Fin h → ℚ_[l], x = ∑ b, qB l (q b) * e b) ∧
      (∀ a b, InE h (M a b)) ∧ (Matrix.of fun (a b : Fin h) => (φ l ^ (a : ℕ)) (e b)) * M = 1

def TriangularCoboundaryFlat : Prop :=
  ∀ (F : Type) [Field F] (G : Type) (s : G → F →+* F) (n : Type) [Fintype n] [DecidableEq n] (c : n → ℤ)
    (cc : G → Matrix n n F) (P Q : Matrix n n F), (∀ g i j, c j < c i → cc g i j = 0) → P * Q = 1 →
    (∀ g, cc g * P.map (s g) = P) →
    ∃ P' Q' : Matrix n n F, P' * Q' = 1 ∧ (∀ i j, c j < c i → P' i j = 0 ∧ Q' i j = 0) ∧
      ∀ g, cc g * P'.map (s g) = P'

def SlopePeriodStableLine : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (h : ℕ), 0 < h → ∃ (z : B l) (χz : GQ l → B l), IsUnit z ∧ Eig h 1 z ∧
    (∀ g, InE h (χz g) ∧ σB g z = χz g * z) ∧ Continuous fun g => th l (ι l (χz g))

def SenPotentiallyUnramified : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Fld l) [FiniteDimensional ℚ_[l] K] (n : ℕ)
    (r : K.fixingSubgroup → Matrix (Fin n) (Fin n) ℚ_[l]) (Q Q' : Matrix (Fin n) (Fin n) ℂ_[l]), Q * Q' = 1 →
    (∀ σ : K.fixingSubgroup, (r σ).map (algebraMap ℚ_[l] ℂ_[l]) * Q.map (σC σ.1) = Q) →
    ∃ (L : Fld l) (hL : K ≤ L), FiniteDimensional ℚ_[l] L ∧
      ∀ σ : L.fixingSubgroup, Ine σ.1 → r ⟨σ.1, fix_mono hL σ⟩ = 1

def SenCoefficientsAdmissible : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (h : ℕ), 0 < h → ∀ (K : Fld l) [FiniteDimensional ℚ_[l] K], FixE h K →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (δ : K.fixingSubgroup → Matrix n n (B l)), (∀ σ i j, InE h (δ σ i j)) →
    (∀ a, ∃ Q Q' : Matrix n n ℂ_[l], Q * Q' = 1 ∧
      ∀ σ : K.fixingSubgroup, (δ σ).map (fun x => th l (iA l a x)) * Q.map (σC σ.1) = Q) →
    ∃ (L : Fld l) (hL : K ≤ L), FiniteDimensional ℚ_[l] L ∧
      ∀ σ : L.fixingSubgroup, Ine σ.1 → δ ⟨σ.1, fix_mono hL σ⟩ = 1

def UnramifiedTrivialisedPeriods : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (h : ℕ), 0 < h → ∀ (K : Fld l) [FiniteDimensional ℚ_[l] K], FixE h K →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (c : n → ℤ) (δ : K.fixingSubgroup → Matrix n n (B l)),
    (∀ σ i j, InE h (δ σ i j)) → (∀ σ i j, c i ≠ c j → δ σ i j = 0) → δ 1 = 1 → (∀ σ τ, δ (σ * τ) = δ σ * δ τ) →
    (∀ i j, Continuous fun σ => th l (ι l (δ σ i j))) → (∀ σ : K.fixingSubgroup, Ine σ.1 → δ σ = 1) →
    ∃ (L : Fld l) (hL : K ≤ L) (U U' : Matrix n n (B l)), FiniteDimensional ℚ_[l] L ∧
      Unr h L (fun σ => δ ⟨σ.1, fix_mono hL σ⟩) U U' ∧ ∀ i j, c i ≠ c j → U i j = 0 ∧ U' i j = 0

def Coc {L : Fld l} {n : ℕ} (r : L.fixingSubgroup → Matrix (Fin n) (Fin n) ℚ_[l])
    (a : L.fixingSubgroup → Fin n → ℚ_[l]) : Prop :=
  Continuous a ∧ ∀ σ τ, a (σ * τ) = a σ + r σ *ᵥ a τ

def CocF {L : Fld l} {n : ℕ} (r : L.fixingSubgroup → Matrix (Fin n) (Fin n) ℚ_[l])
    (a : L.fixingSubgroup → Fin n → ℚ_[l]) : Prop :=
  ∃ γ : Fin n → B l, ∀ σ : L.fixingSubgroup,
    (fun i => qB l (a σ i)) = (r σ).map (qB l) *ᵥ (fun i => σB σ.1 (γ i)) - γ

structure Crys {L : Fld l} {n : ℕ} (r : L.fixingSubgroup → Matrix (Fin n) (Fin n) ℚ_[l]) : Prop where
  one : r 1 = 1
  mul : ∀ σ τ, r (σ * τ) = r σ * r τ
  cont : Continuous r
  per : ∃ P Q : Matrix (Fin n) (Fin n) (B l), P * Q = 1 ∧
    ∀ σ : L.fixingSubgroup, (r σ).map (qB l) * P.map (σB σ.1) = P

def BlochKatoDualityMatrices : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : Fld l) [FiniteDimensional ℚ_[l] L] (n : ℕ)
    (r r' : L.fixingSubgroup → Matrix (Fin n) (Fin n) ℚ_[l]), Crys r → Crys r' →
    (∀ σ : L.fixingSubgroup, (r σ)ᵀ * r' σ = χ σ.1 • (1 : Matrix (Fin n) (Fin n) ℚ_[l])) →
    ∀ a, Coc r a → (∀ b, Coc r' b → CocF r' b → ∃ f : L.fixingSubgroup → ℚ_[l], Continuous f ∧
      ∀ σ τ, a σ ⬝ᵥ (r' σ *ᵥ b τ) = χ σ.1 * f τ - f (σ * τ) + f σ) → CocF r a

def GeometricEqualsFinite : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : Fld l) [FiniteDimensional ℚ_[l] L] (n : ℕ)
    (r r' : L.fixingSubgroup → Matrix (Fin n) (Fin n) ℚ_[l]), Crys r → Crys r' →
    (∀ σ : L.fixingSubgroup, (r σ)ᵀ * r' σ = χ σ.1 • (1 : Matrix (Fin n) (Fin n) ℚ_[l])) →
    (∀ x : Fin n → B l, (∀ σ : L.fixingSubgroup, (r' σ).map (qB l) *ᵥ (fun i => σB σ.1 (x i)) = x) →
      (∀ i, φ l (x i) = x i) → x = 0) →
    ∀ a, Coc r a → (∃ α : Fin n → BdR l, (∀ i, α i ∈ Plus l) ∧ ∀ σ : L.fixingSubgroup,
      (fun i => qQ l (a σ i)) = (r σ).map (qQ l) *ᵥ (fun i => σD σ.1 (α i)) - α) → CocF r a

def PrimitiveFrobeniusFixed : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : Fld l) [FiniteDimensional ℚ_[l] L] (n : ℕ)
    (r : L.fixingSubgroup → Matrix (Fin n) (Fin n) ℚ_[l]), Crys r →
    (∀ x : Fin n → B l, (∀ σ : L.fixingSubgroup, (r σ).map (qB l) *ᵥ (fun i => σB σ.1 (x i)) = x) →
      (∀ i, φ l (x i) = x i) → x = 0) →
    ∀ a, CocF r a → ∃ γ : Fin n → B l, (∀ i, φ l (γ i) = γ i) ∧ ∀ σ : L.fixingSubgroup,
      (fun i => qB l (a σ i)) = (r σ).map (qB l) *ᵥ (fun i => σB σ.1 (γ i)) - γ

def CohomologyTwistDecomposition : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : Fld l) [FiniteDimensional ℚ_[l] L] (n : ℕ)
    (r : L.fixingSubgroup → Matrix (Fin n) (Fin n) ℚ_[l]) (U U' : Matrix (Fin n) (Fin n) (B l)),
    (∀ i j, U i j ∈ Ainf' l ∧ U' i j ∈ Ainf' l) → U * U' = 1 →
    (∀ σ : L.fixingSubgroup, (r σ).map (qB l) * U.map (σB σ.1) = U) → (∀ σ : L.fixingSubgroup, Ine σ.1 → r σ = 1) →
    ∀ a, Coc (fun σ => χ σ.1 • r σ) a → ∃ w : Fin n → ℚ_[l], (∀ σ, r σ *ᵥ w = w) ∧
      CocF (fun σ => χ σ.1 • r σ) (fun σ => a σ - κ σ.1 • w)

def SlopeDifferenceExtension : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (h : ℕ), 0 < h → ∀ (L : Fld l) [FiniteDimensional ℚ_[l] L], FixE h L →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (δ : L.fixingSubgroup → Matrix n n (B l)) (U U' : Matrix n n (B l)),
    Unr h L δ U U' → (∀ σ : L.fixingSubgroup, Ine σ.1 → δ σ = 1) →
    ∀ (m : ℤ), 0 < m → ∀ x : L.fixingSubgroup → n → B l, (∀ σ i, Eig h m (x σ i)) →
    (∀ a, ∃ y : n → BdR l, ∀ σ : L.fixingSubgroup,
      (fun i => iA l a (x σ i)) = (δ σ).map (iA l a) *ᵥ (fun i => σD σ.1 (y i)) - y) →
    ∃ γ w : n → B l, (∀ i, Eig h m (γ i)) ∧ (∀ i, InE h (w i)) ∧ (∀ σ, δ σ *ᵥ w = w) ∧ (m ≠ h → w = 0) ∧
      ∀ σ : L.fixingSubgroup,
        x σ = δ σ *ᵥ (fun i => σB σ.1 (γ i)) - γ + (qB l (κ σ.1) * t l) • w

structure Gr (h : ℕ) (L : Fld l) {d : ℕ} (c : Fin d → ℤ) (cc δ : L.fixingSubgroup → Matrix (Fin d) (Fin d) (B l))
    (U U' : Matrix (Fin d) (Fin d) (B l)) : Prop where
  pos : 0 < h
  fix : FixE h L
  eig : ∀ σ i j, Eig h (c j - c i) (cc σ i j)
  tri : ∀ σ i j, c j < c i → cc σ i j = 0
  diag : ∀ σ i j, δ σ i j = if c i = c j then cc σ i j else 0
  unr : Unr h L δ U U'
  ine : ∀ σ : L.fixingSubgroup, Ine σ.1 → δ σ = 1
  blk : ∀ i j, c i ≠ c j → U i j = 0 ∧ U' i j = 0
  flat : ∀ a, ∃ P Q : Matrix (Fin d) (Fin d) (BdR l), P * Q = 1 ∧
    ∀ σ : L.fixingSubgroup, (cc σ).map (iA l a) * P.map (σD σ.1) = P

def DeRhamGradedCocycle : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Fld l) [FiniteDimensional ℚ_[l] K] (d : ℕ)
    (ρ : K.fixingSubgroup →* GL (Fin d) ℚ_[l]), IsDRPlus K ρ →
    ∃ (L : Fld l) (hL : K ≤ L) (h : ℕ) (c : Fin d → ℤ) (cc δ : L.fixingSubgroup → Matrix (Fin d) (Fin d) (B l))
      (U U' W W' : Matrix (Fin d) (Fin d) (B l)), FiniteDimensional ℚ_[l] L ∧ Gr h L c cc δ U U' ∧ W * W' = 1 ∧
      ∀ σ : L.fixingSubgroup,
        (ρ ⟨σ.1, fix_mono hL σ⟩ : Matrix (Fin d) (Fin d) ℚ_[l]).map (qB l) * W.map (σB σ.1) = W * cc σ

def GradedCocycleCoboundary : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : Fld l) [FiniteDimensional ℚ_[l] L] (h d : ℕ) (c : Fin d → ℤ)
    (cc δ : L.fixingSubgroup → Matrix (Fin d) (Fin d) (B l)) (U U' : Matrix (Fin d) (Fin d) (B l)),
    Gr h L c cc δ U U' → ∃ P Q : Matrix (Fin d) (Fin d) (BdR l), (∀ i j, P i j ∈ Bst l ∧ Q i j ∈ Bst l) ∧
      P * Q = 1 ∧ ∀ σ : L.fixingSubgroup, (cc σ).map (ι l) * P.map (σD σ.1) = P

end period_ring_base
