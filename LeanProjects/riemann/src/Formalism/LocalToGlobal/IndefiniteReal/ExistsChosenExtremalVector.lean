import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.FWT

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.Datum Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Idx

variable {n : ℕ} (ε : Fin n → Bool)

def negS : Finset (Fin n) := Finset.univ.filter fun a => ε a = false

def nNeg : ℕ := (negS ε).card

theorem nNeg_le : nNeg ε ≤ n := (Finset.card_le_univ _).trans (Fintype.card_fin n).le

def revOn : Equiv.Perm {a // a ∈ negS ε} :=
  (((negS ε).orderIsoOfFin rfl).toEquiv.symm.trans Fin.revPerm).trans ((negS ε).orderIsoOfFin rfl).toEquiv

def revNeg : Equiv.Perm (Fin n) := Equiv.Perm.ofSubtype (revOn ε)

theorem revNeg_of_pos {a : Fin n} (h : ε a = true) : revNeg ε a = a :=
  Equiv.Perm.ofSubtype_apply_of_not_mem _ (by simp [negS, h])

theorem eps_revNeg (a : Fin n) : ε (revNeg ε a) = ε a := by
  by_cases h : a ∈ negS ε
  · have h1 : revNeg ε a = (revOn ε ⟨a, h⟩ : Fin n) := Equiv.Perm.ofSubtype_apply_of_mem _ h
    have h2 := (revOn ε ⟨a, h⟩).2
    rw [h1]
    simp only [negS, Finset.mem_filter, Finset.mem_univ, true_and] at h h2
    exact h2.trans h.symm
  · rw [show revNeg ε a = a from Equiv.Perm.ofSubtype_apply_of_not_mem _ h]

def arr (q : ℕ) (c : Fin n) : Fin n :=
  if h : (c : ℕ) < q then ⟨n - 1 - c, by have := c.2; omega⟩ else ⟨c - q, by have := c.2; omega⟩

variable {ε}

theorem nNeg_shape {p : ℕ} (hp : p ≤ n) (h : ∀ a, ε a = decide ((a : ℕ) < p)) : nNeg ε = n - p := by
  have e : negS ε = Finset.univ.map ⟨fun i : Fin (n - p) => (⟨p + i, by have := i.2; omega⟩ : Fin n),
      fun i j hij => Fin.ext (by have := congrArg Fin.val hij; simp only at this; omega)⟩ := by
    ext a
    simp only [negS, Finset.mem_filter, Finset.mem_univ, true_and, h, decide_eq_false_iff_not, Finset.mem_map]
    constructor
    · intro ha
      exact ⟨⟨a - p, by have := a.2; omega⟩, Fin.ext (show p + ((a : ℕ) - p) = a by omega)⟩
    · rintro ⟨i, rfl⟩
      show ¬ (p + (i : ℕ) < p)
      omega
  rw [nNeg, e, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem revNeg_shape {p : ℕ} (hp : p ≤ n) (h : ∀ a, ε a = decide ((a : ℕ) < p)) (a : Fin n) :
    (revNeg ε a : ℕ) = if (a : ℕ) < p then (a : ℕ) else n - 1 - (a - p) := by
  split_ifs with ha
  · rw [revNeg_of_pos ε (by simp [h, ha])]
  · have hq : (negS ε).card = n - p := nNeg_shape hp h
    have hm : a ∈ negS ε := by simpa [negS, h] using ha
    have hf : ∀ i : Fin (negS ε).card, (((negS ε).orderEmbOfFin rfl i : Fin n) : ℕ) = p + i := by
      have := Finset.orderEmbOfFin_unique (s := negS ε) (rfl : (negS ε).card = _)
        (f := fun i : Fin (negS ε).card => (⟨p + i, by have := i.2; omega⟩ : Fin n))
        (fun i => by simp [negS, h]) (fun i j hij => by
          show p + (i : ℕ) < p + j
          have : (i : ℕ) < j := hij
          omega)
      intro i
      rw [← this]
    have h1 : revNeg ε a = (revOn ε ⟨a, hm⟩ : Fin n) := Equiv.Perm.ofSubtype_apply_of_mem _ hm
    set i := ((negS ε).orderIsoOfFin rfl).symm ⟨a, hm⟩ with hi
    have h2 : (a : ℕ) = p + i := by
      rw [← hf i]
      have : ((negS ε).orderIsoOfFin rfl i : Fin n) = a := by rw [hi, OrderIso.apply_symm_apply]
      rw [← this]; rfl
    have h3 : ((revOn ε ⟨a, hm⟩ : Fin n) : ℕ) = p + (Fin.rev i : ℕ) := hf (Fin.rev i)
    rw [h1, h3, Fin.val_rev]
    have := i.2
    omega

theorem revNeg_arr {p : ℕ} (hp : p ≤ n) (h : ∀ a, ε a = decide ((a : ℕ) < p)) (c : Fin n) :
    (revNeg ε (arr (nNeg ε) c) : ℕ) = if (c : ℕ) < n - p then p + c else c - (n - p) := by
  have := c.2
  rw [revNeg_shape hp h, nNeg_shape hp h]
  unfold arr
  split_ifs <;> simp only at * <;> omega

end Idx

section Ext

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

def extWt (τ : D.what₂.Tau) : Fin V.rank → ℝ := fun a => Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ) (revNeg (M.ε τ) a)

def IsExtVec (v : M.Vec) : Prop :=
  ∀ τ, ‖(v τ : M.H τ)‖ = 1 ∧ v τ ∈ lowT M τ ∧ IsWtOn (Formalism.REAL.Kset (M.ε τ)) (M.σ τ) (extWt M τ) (v τ : M.H τ)

def ExtLine : Prop :=
  ∀ v v', IsExtVec M v → IsExtVec M v' → ∀ τ, ∃ c : ℂ, ‖c‖ = 1 ∧ v' τ = c • v τ

def LowSm : Prop := ∀ τ, lowKSub (M.ε τ) (M.lam τ) (M.σ τ) ≤ M.sm τ

def x0Mat (τ : D.what₂.Tau) : Matrix (Fin V.rank) (Fin V.rank) ℂ := (onb M τ).submatrix id (arr (nNeg (M.ε τ)))

theorem torus_x0Mat (τ : D.what₂.Tau) (t : Fin V.rank → ℂ) :
    (M.fr τ)⁻¹ * diagonal t * M.fr τ * x0Mat M τ = x0Mat M τ * diagonal (fun c => t (arr (nNeg (M.ε τ)) c)) := by
  have hinv : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ))
  have h1 : (M.fr τ)⁻¹ * diagonal t * M.fr τ * x0Mat M τ =
      ((M.fr τ)⁻¹ * diagonal t * M.fr τ * (M.fr τ)⁻¹).submatrix id (arr (nNeg (M.ε τ))) := rfl
  rw [h1, Matrix.mul_assoc _ (M.fr τ), hinv, Matrix.mul_one]
  ext a c
  simp only [submatrix_apply, id, mul_diagonal, x0Mat, onb]

theorem extWt_arr (τ : D.what₂.Tau) {p : ℕ} (hp : p ≤ V.rank) (h : ∀ a, M.ε τ a = decide ((a : ℕ) < p)) (c a : Fin V.rank)
    (ha : (a : ℕ) = if (c : ℕ) < V.rank - p then p + c else c - (V.rank - p)) :
    extWt M τ (arr (nNeg (M.ε τ)) c) = Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ) a := by
  unfold extWt
  congr 1
  exact Fin.ext ((revNeg_arr hp h c).trans ha.symm)

end Ext

section ExtEx

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def pM (π : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℂ := (1 : Matrix (Fin n) (Fin n) ℂ).submatrix π id

theorem diag_pM (π : Equiv.Perm (Fin n)) (t : Fin n → ℂ) : diagonal (fun a => t (π a)) * pM π = pM π * diagonal t := by
  ext a b
  simp only [diagonal_mul, mul_diagonal, pM, submatrix_apply, id, one_apply]
  split_ifs with h
  · rw [h, mul_comm]
  · simp

theorem pM_mem (π : Equiv.Perm (Fin n)) (h : ∀ a, ε (π a) = ε a) : pM π ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, pM, conjTranspose_submatrix, conjTranspose_one]
    have := Matrix.submatrix_mul_equiv (1 : Matrix (Fin n) (Fin n) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ) π (Equiv.refl (Fin n)) π
    simp only [Equiv.coe_refl, Matrix.mul_one] at this
    rw [this, submatrix_one_equiv]
  · have := diag_pM π (fun a => if ε a then (1 : ℂ) else -1)
    simp only [h] at this
    exact this.symm

theorem kset_uj {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) : g ∈ UJset ε := by
  show gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
  have h1 : gᴴ * g = 1 := (Matrix.mem_unitaryGroup_iff').1 hg.1
  rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem diag_mem (θ : Fin n → ℝ) : diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    simp only [Pi.star_apply, RCLike.star_def]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
    simp
  · unfold Formalism.REAL.Jm
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext a
    exact mul_comm _ _

theorem isWtOn_perm (hσ : IsURepOn (UJset ε) σ) (π : Equiv.Perm (Fin n)) (h : ∀ a, ε (π a) = ε a) {μ : Fin n → ℝ} {w : H}
    (hw : IsWtOn (Formalism.REAL.Kset ε) σ μ w) : IsWtOn (Formalism.REAL.Kset ε) σ (fun a => μ (π a)) (σ (pM π) w) := by
  intro θ _
  have hd := diag_pM π (fun b => Complex.exp ((θ (π.symm b) : ℂ) * Complex.I))
  simp only [Equiv.symm_apply_apply] at hd
  have m1 := hσ.1.2 _ (kset_uj (diag_mem (ε := ε) θ)) _ (kset_uj (pM_mem π h))
  have m2 := hσ.1.2 _ (kset_uj (pM_mem π h)) _ (kset_uj (diag_mem (ε := ε) fun b => θ (π.symm b)))
  have e1 : σ (diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) (σ (pM π) w) =
      σ (pM π) (σ (diagonal fun b => Complex.exp ((θ (π.symm b) : ℂ) * Complex.I)) w) := by
    rw [← ContinuousLinearMap.comp_apply, ← m1, hd, m2, ContinuousLinearMap.comp_apply]
  rw [e1, hw _ (diag_mem _), map_smul]
  congr 4
  exact (Equiv.sum_comp π fun b => μ b * θ (π.symm b)).symm.trans (by simp)

theorem isWtOn_smul {G : Set (Matrix (Fin n) (Fin n) ℂ)} {μ : Fin n → ℝ} {w : H} (hw : IsWtOn G σ μ w) (c : ℂ) :
    IsWtOn G σ μ (c • w) := by
  intro θ hθ
  rw [map_smul, hw θ hθ, smul_comm]

theorem exists_ext {lam : Fin n → ℝ} (hσ : IsDS ε lam σ) : ∃ w : H, ‖w‖ = 1 ∧ w ∈ lowKSub ε lam σ ∧
    IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) w := by
  obtain ⟨-, -, hU, -, -, ⟨S, hS⟩, -⟩ := hσ
  obtain ⟨v, hvS, hv0, hv⟩ := hS.2.2.2.1
  have hK := pM_mem (revNeg ε) (eps_revNeg ε)
  have hn : ‖σ (pM (revNeg ε)) v‖ = ‖v‖ := hU.2.1 _ (kset_uj hK) v
  have hp : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
  refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • σ (pM (revNeg ε)) v, ?_, ?_, isWtOn_smul (isWtOn_perm hU _ (eps_revNeg ε) hv) _⟩
  · rw [norm_smul, hn, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hp]
  · exact Submodule.smul_mem _ _ ((le_sSup (s := {S | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S}) hS) (hS.2.1 _ hK v hvS))

end ExtEx

theorem exists_isExtVec {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (h : LowSm M) :
    ∃ v, IsExtVec M v := by
  choose w hw using fun τ => exists_ext (M.ds τ)
  exact ⟨fun τ => ⟨w τ, h τ (hw τ).2.1⟩, fun τ => ⟨(hw τ).1, (hw τ).2.1, (hw τ).2.2⟩⟩

section Base

open ReciprocityTheory.ChartRestriction.G.FD

variable {D : D7} {r : ℕ} {Comp : Type} {X : Comp → Data D.host.E r}

def FrAt {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (θ : InfFam D) (hr : V.rank = r)
    (dict : GA D V → Σ k, Frame (X k).Ψ r) (γ h : GA D V) : Prop :=
  ∀ (ρ : D.what₂.Tau) (τ : (X (dict h).1).Ψ), τ.1 = tauE D ρ →
    mat (dict h).2 τ = Matrix.reindex (finCongr hr) (finCongr hr) (archM V (θ ρ) (γ * h) * x0Mat M ρ)

def BaseFr {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (θ : InfFam D) (hr : V.rank = r)
    (dict : GA D V → Σ k, Frame (X k).Ψ r) : Prop :=
  (∀ k (τ : D.host.E →+* ℂ), τ ∈ (X k).Ψ ↔ ∃ ρ, τ = tauE D ρ) ∧ (∀ k ρ, (X k).p0 = nNeg (M.ε ρ)) ∧
    ∀ h, ∃ γ ∈ GQ V, FrAt M θ hr dict γ h ∧ ∀ u ∈ GinfC V, ∃ γ' ∈ (X (dict h).1).Γ, ∃ x : Frame (X (dict h).1).Ψ r,
      dict (h * u) = ⟨(dict h).1, lact γ' x⟩ ∧ ∀ (ρ : D.what₂.Tau) (τ : (X (dict h).1).Ψ), τ.1 = tauE D ρ →
        mat x τ = Matrix.reindex (finCongr hr) (finCongr hr) (archM V (θ ρ) (γ * h * u) * x0Mat M ρ)

def IsModelBaseFrameFamily {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (hr : V.rank = r)
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∀ ρ, x₀ (tauE D ρ) = Matrix.reindex (finCongr hr) (finCongr hr) (x0Mat M ρ)

theorem IsModelBaseFrameFamily.mul {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {hr : V.rank = r}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} (h : IsModelBaseFrameFamily M hr x₀) (ρ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    Matrix.reindex (finCongr hr) (finCongr hr) g * x₀ (tauE D ρ) =
      Matrix.reindex (finCongr hr) (finCongr hr) (g * x0Mat M ρ) := by
  rw [h ρ]
  exact Matrix.submatrix_mul_equiv g (x0Mat M ρ) _ (finCongr hr).symm _

def castDict {Y : Type} {V W : HSp D} (hV : V = W) (dict : GA D V → Y) : GA D W → Y :=
  fun g => dict (cast (congrArg (GA D) hV.symm) g)

theorem archM_eq (V : HSp D) (th : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (h : GA D V) :
    archM V th h = infMat D.sp.cm.sig V.gram th h := rfl

end Base

section Collected

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem rank_Wc (i : Fin D.R.m) : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2

def ExtremalVectorPairsToDelta (i : Fin D.R.m) (v : (R.MW i (sg0 D A)).Vec) : Prop :=
  ∃ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (w : (R.cV i).W), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v ρ) ∧ ‖w‖ = 1 ∧
    R.ioP i (PiTensorProduct.tprod ℂ u) w = RealDat.Delta i

def IsChosenExtremalVector (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : (R.MW i σ).Vec) : Prop :=
  IsExtVec (R.MW i σ) v ∧ ∀ h : σ = sg0 D A, (∃ u, IsExtVec (R.MW i (sg0 D A)) u ∧ ExtremalVectorPairsToDelta R i u) → ExtremalVectorPairsToDelta R i (h ▸ v)

def IoExt : Prop := ∀ i, ∃ u, IsExtVec (R.MW i (sg0 D A)) u ∧ ExtremalVectorPairsToDelta R i u

theorem exists_chosen_extremal_vector (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (h : LowSm (R.MW i σ)) : ∃ v, IsChosenExtremalVector R i σ v := by
  by_cases hσ : σ = sg0 D A
  · subst hσ
    by_cases hu : ∃ u, IsExtVec (R.MW i (sg0 D A)) u ∧ ExtremalVectorPairsToDelta R i u
    · obtain ⟨u, h1, h2⟩ := hu
      exact ⟨u, h1, fun _ _ => h2⟩
    · obtain ⟨v, hv⟩ := exists_isExtVec _ h
      exact ⟨v, hv, fun _ h' => absurd h' hu⟩
  · obtain ⟨v, hv⟩ := exists_isExtVec _ h
    exact ⟨v, hv, fun h' => absurd h' hσ⟩

open Classical in

def v0 (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) : (R.MW i σ).Vec :=
  if h : ∃ v, IsChosenExtremalVector R i σ v then h.choose else 0

theorem extremal_vector_is_chosen (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (h : LowSm (R.MW i σ)) : IsChosenExtremalVector R i σ (v0 R i σ) := by
  have h' := exists_chosen_extremal_vector R i σ h
  unfold v0
  rw [dif_pos h']
  exact h'.choose_spec

theorem IsChosenExtremalVector.norm {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} {v : (R.MW i σ).Vec} (h : IsChosenExtremalVector R i σ v) (τ : D.what₂.Tau) :
    ‖(v τ : (R.MW i σ).H τ)‖ = 1 := (h.1 τ).1

theorem IsChosenExtremalVector.io {i : Fin D.R.m} {v : (R.MW i (sg0 D A)).Vec} (h : IsChosenExtremalVector R i (sg0 D A) v) (hio : IoExt R) : ExtremalVectorPairsToDelta R i v :=
  h.2 rfl (hio i)

def JConj : Prop :=
  ∀ i (σ : D.what₂.LL →+* ℂ) (x y : Fin (R.nW i) → D.what₂.LL),
    ⟪(R.FW i).j ((starRingEnd ℂ).comp σ) x, (R.FW i).j ((starRingEnd ℂ).comp σ) y⟫_ℂ =
      starRingEnd ℂ ⟪(R.FW i).j σ x, (R.FW i).j σ y⟫_ℂ

end Collected

def BaseFrT {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    (T : Core D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) : Prop :=
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) →
    ∀ hV : T.V ((i : ℕ) + 1) (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) = Wc D i,
      BaseFr (R.MW i σ) R.θ (rank_Wc i)
        (castDict hV (T.dict ((i : ℕ) + 1) (σ.comp (algebraMap T.Q.c.F D.what₂.LL))))

end Formalism.IndefR.FWT
