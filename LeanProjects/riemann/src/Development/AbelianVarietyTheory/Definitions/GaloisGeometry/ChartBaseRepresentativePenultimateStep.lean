import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie

noncomputable section

namespace GlobalTheory.TwV.Model

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  {A : AdData t u μ St} {dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt} {a : 𝓞 D.host.E}

theorem isPtAd_rep (H : AdTie A dtU a) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.chTw u μ).cls i) :
    IsPtAd A a i hi ((St i hi).chOf c) ((St i hi).y c) (A.pt i hi c) where
  lat := by
    rw [← H.N_eq i hi c]
    exact H.lat i hi c
  frame P := H.frame i hi c P
  fnl P v h hv := by
    obtain ⟨ι, hι⟩ := H.fnl i hi ((St i hi).chOf c) P v h hv
    exact Classical.epsilon_spec
      (p := fun ι => ∀ c', (St i hi).chOf c' = (St i hi).chOf c →
        FunMoved t.seam ((St i hi).K ((St i hi).chOf c)).lev P v h ι (A.mov i hi c') (A.pt i hi c').deco.1) ⟨ι, hι⟩ c rfl

theorem exists_isPtAd (H : AdTie A dtU a) (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) : ∃ x p, IsPtAd A a i hi β x p := by
  obtain ⟨⟨c, rfl⟩, -⟩ := ((St i hi).K β).y_bij.2 (Quotient.mk'' 1)
  exact ⟨_, _, isPtAd_rep H i hi c⟩

theorem muOf_det (j : ℕ) (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) :
    muOf t u μ dtU j (Matrix.GeneralLinearGroup.det y.1) = (((t.O u μ).mt j (dtU y) : ℂˣ) : ℂ) := by
  have h : ∃ y' : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y'.1 = Matrix.GeneralLinearGroup.det y.1 := ⟨y, rfl⟩
  have e : h.choose = y := by
    have hc := congrArg Units.val h.choose_spec
    simp only [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique] at hc
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i
    fin_cases j
    exact hc
  unfold muOf
  rw [dif_pos h, e]

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {w : Pr.Word}

open Classical in

theorem frsF_mem {j : ℕ} (p : ChPt (R := R) sel mu w j) (P : rowSG Pr sel mu) (x : Sp X.E (R.N j)) :
    frsF sel mu p P x ∈ p.deco.1.at P.1 ↔ x ∈ stdAt X.E (R.N j) P.1 := by
  unfold frsF
  split_ifs with h
  · exact (Deco.liftFr_spec (p.deco.2.hasLift ⟨P.1, h⟩)).1 x
  · exact p.2 ⟨P.1, (Finset.mem_union.mp P.2).resolve_left h⟩ x

private theorem mem_stdAt_iff_forall_intAt {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (w : Sp X.E n) :
    w ∈ stdAt X.E n P ↔ ∀ l, IntAt P (w l) := by
  show (∃ s ∈ P.asIdeal.primeCompl, s • w ∈ _) ↔ _
  constructor
  · rintro ⟨s, hs, hsw⟩ l
    obtain ⟨r, hr⟩ := (Submodule.mem_one).1 (hsw l (Set.mem_univ l))
    refine ⟨r, s, hs, ?_⟩
    rw [hr]
    simp [Algebra.smul_def]
  · intro h
    choose r s hs e using h
    refine ⟨∏ l, s l, Submonoid.prod_mem _ fun l _ => hs l, fun l _ => ?_⟩
    change ((∏ l, s l) • w) l ∈ (1 : Submodule (𝓞 X.E) X.E)
    rw [Submodule.mem_one]
    refine ⟨r l * ∏ k ∈ Finset.univ.erase l, s k, ?_⟩
    rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ l)]
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul, map_prod]
    rw [← e l]
    ring

open Classical in

theorem sameCoset_iff {j : ℕ} (p : ChPt (R := R) sel mu w j) (P : rowSG Pr sel mu) (z y : Sp X.E (R.N j)) :
    SameCoset sel mu cst P ((frsF sel mu p P).symm z) ((frsF sel mu p P).symm y) ↔
      (((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then (0 : ℤ) else (cst.M : ℤ)))⁻¹ • (z - y)) ∈ p.deco.1.at P.1 := by
  have hc : ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ =
      ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then (0 : ℤ) else (cst.M : ℤ)))⁻¹ := by
    split_ifs <;> simp
  have e : ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then (0 : ℤ) else (cst.M : ℤ)))⁻¹ • (z - y) =
      frsF sel mu p P (((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then (0 : ℤ) else (cst.M : ℤ)))⁻¹ •
        ((frsF sel mu p P).symm z - (frsF sel mu p P).symm y)) := by
    rw [map_smul, map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rw [e, frsF_mem, mem_stdAt_iff_forall_intAt]
  unfold SameCoset
  simp only [hc, Pi.smul_apply, smul_eq_mul]

theorem sameCoset_trans {n : ℕ} {P : rowSG Pr sel mu} {x y z : Sp X.E n} (h : SameCoset sel mu cst P x y) (h' : SameCoset sel mu cst P y z) :
    SameCoset sel mu cst P x z := by
  intro l
  obtain ⟨r₁, s₁, hs₁, e₁⟩ := h l
  obtain ⟨r₂, s₂, hs₂, e₂⟩ := h' l
  refine ⟨r₁ * s₂ + r₂ * s₁, s₁ * s₂, fun hm => (P.1.isPrime.mem_or_mem hm).elim hs₁ hs₂, ?_⟩
  simp only [Pi.sub_apply] at e₁ e₂ ⊢
  rw [map_add, map_mul, map_mul, map_mul, ← e₁, ← e₂]
  ring

theorem sameCoset_symm {n : ℕ} {P : rowSG Pr sel mu} {x y : Sp X.E n} (h : SameCoset sel mu cst P x y) :
    SameCoset sel mu cst P y x := by
  intro l
  obtain ⟨r, s, hs, e⟩ := h l
  refine ⟨-r, s, hs, ?_⟩
  simp only [Pi.sub_apply] at e ⊢
  rw [map_neg, ← e]
  ring

theorem mem_of_ybSet {j : ℕ} (p : ChPt (R := R) sel mu w j) {Yb : Set (Sp X.E (R.N j))} (h : Yb ∈ ybSet sel mu cst p.deco.1.N) :
    ∃ y ∈ Yb, ∀ z, z ∈ Yb ↔ ∀ P, SameCoset sel mu cst P ((frsF sel mu p P).symm z) ((frsF sel mu p P).symm y) := by
  obtain ⟨y, -, rfl⟩ := h
  refine ⟨y, ?_, fun z => ?_⟩
  · show y - y ∈ locLat (rowSG Pr sel mu) p.deco.1.N _
    rw [sub_self]
    exact Submodule.zero_mem _
  · show z - y ∈ locLat (rowSG Pr sel mu) p.deco.1.N _ ↔ _
    unfold locLat
    rw [Submodule.mem_iInf]
    refine forall_congr' fun P => ?_
    rw [Submodule.mem_comap, sameCoset_iff]
    rfl

end Gen

theorem chartBaseRepresentative_penultimate_step (β : (St (t.m2 + 1) (cpl_lt t μ).le).Ch) (P : SB t μ) : y0At A (t.m2 + 1) (cpl_lt t μ).le β P = A.y0 β P := by
  unfold y0At
  rw [dif_pos rfl]

theorem cosetOf_rep (H : AdTie A dtU a) (c : (D.chTw u μ).cls (t.m2 + 1)) :
    cosetOf A (t.m2 + 1) (cpl_lt t μ).le ((St _ (cpl_lt t μ).le).chOf c) (A.pt _ (cpl_lt t μ).le c) = A.yb c := by
  obtain ⟨y₀, hy₀, hmem⟩ := mem_of_ybSet t.sel (t.tup μ) (t.cst μ) (A.pt _ (cpl_lt t μ).le c) (H.chain.2.1 c)
  ext z
  simp only [cosetOf, Set.mem_ofPred_eq, chartBaseRepresentative_penultimate_step]
  constructor
  · intro hz
    rw [hmem]
    intro P
    exact sameCoset_trans _ _ _ (hz P) (sameCoset_symm _ _ _ (H.coset c y₀ hy₀ P))
  · intro hz P
    exact H.coset c z hz P

theorem xiPt_rep (H : AdTie A dtU a) (i : ℕ) (hi : i + 1 ≤ D.R.m) (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1))
    (z : HomE t.X.E (D.R.N i) (D.R.N (i + 1))) :
    t.seam.σ₀ (xiPt A i hi ((St i _).chOf c) ((St (i + 1) hi).chOf c') (A.pt i (Nat.le_of_succ_le hi) c) (A.pt (i + 1) hi c') z) =
      (t.rd u μ).Xi i c c' z := by
  unfold xiPt
  split_ifs with h₁ h₂
  · rw [H.chain.2.2.1 i h₁ c c' z]
  · subst h₂
    rw [H.chain.2.2.2.1 c c' z, ← cosetOf_rep H c']
  · have h₃ : i = t.m2 + 1 := by
      have := m_eq t μ
      omega
    subst h₃
    rw [H.chain.2.2.2.2.1.2 c c' z, ← cosetOf_rep H c]

theorem xiAd_rep (H : AdTie A dtU a) (i : ℕ) (hi : i + 1 ≤ D.R.m) (hA : PtAway A a i hi)
    (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) (z : HomE D.host.E (D.R.N i) (D.R.N (i + 1))) :
    xiAd A a i hi ((St i _).chOf c) ((St (i + 1) hi).chOf c') ((St i _).y c) ((St (i + 1) hi).y c') z =
      (t.rd u μ).Xi i c c' (seamHom t.seam (inFr
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z)) := by
  have h₁ := isPtAd_rep H i (Nat.le_of_succ_le hi) c
  have h₂ := isPtAd_rep H (i + 1) hi c'
  unfold xiAd
  split
  · next h =>
    rw [hA _ _ _ _ _ _ _ _ _ _ h₁ h₂ h.1.choose_spec h.2.choose_spec (fun _ _ => ⟨rfl, rfl⟩)]
    exact xiPt_rep H i hi c c' _
  · next h => exact absurd ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩ h

theorem exists_det_eq {B : Type} [CommRing B] {n : ℕ} (σ : B →+* B) (J : Matrix (Fin n) (Fin n) B) (hJ : IsUnit J.det)
    (g : GL (Fin n) B) (hg : g ∈ UJ σ J) :
    ∃ y ∈ UJ σ (1 : Matrix (Fin 1) (Fin 1) B), Matrix.GeneralLinearGroup.det y = Matrix.GeneralLinearGroup.det g := by
  have key : σ (g : Matrix (Fin n) (Fin n) B).det * (g : Matrix (Fin n) (Fin n) B).det = 1 := by
    have e := congrArg Matrix.det (show cT σ (g : Matrix (Fin n) (Fin n) B) * J * (g : Matrix (Fin n) (Fin n) B) = J from hg)
    have hs : (cT σ (g : Matrix (Fin n) (Fin n) B)).det = σ (g : Matrix (Fin n) (Fin n) B).det := by
      rw [cT, Matrix.det_transpose, RingHom.map_det]
      rfl
    rw [Matrix.det_mul, Matrix.det_mul, hs] at e
    apply hJ.mul_right_cancel
    rw [one_mul]
    calc σ (g : Matrix (Fin n) (Fin n) B).det * (g : Matrix (Fin n) (Fin n) B).det * J.det
        = σ (g : Matrix (Fin n) (Fin n) B).det * J.det * (g : Matrix (Fin n) (Fin n) B).det := by ring
      _ = J.det := e
  refine ⟨Units.map (Matrix.scalar (Fin 1) : B →+* Matrix (Fin 1) (Fin 1) B).toMonoidHom (Matrix.GeneralLinearGroup.det g), ?_, ?_⟩
  · show cT σ _ * 1 * _ = 1
    ext i j
    fin_cases i
    fin_cases j
    simp [cT, Matrix.mul_apply, Matrix.GeneralLinearGroup.val_det_apply, key]
  · apply Units.ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique]

theorem adLawAt_of_clauses (Hp : AdPins A dtU) (H : AdTie A dtU a) (hE : PtEx A a) (hA : ∀ i hi, PtAway A a i hi) (hL : ∀ i hi, LevAt A dtU a i hi)
    (hR : RatLaw A a) (hS : SizeLaw A a) (hM : MuLaw t u μ dtU)
    (hI : ∀ i hi β β' x x' z, IntOff (t.O u μ).S (xiAd A a i hi β β' x x' z)) :
    AdLawAt A dtU a (xiAd A a) (muOf t u μ dtU) where
  read i hi c c' z := xiAd_rep H i hi (hA i hi) c c' z
  rat := hR
  lev i hi := hL i hi
  away i hi β β' x x' x₁ x₁' hx := by
    funext z
    unfold xiAd
    rw [dif_pos ⟨hE _ _ β x₁, hE _ _ β' x₁'⟩, dif_pos ⟨hE _ _ β x, hE _ _ β' x'⟩]
    rw [hA i hi β β' x x' x₁ x₁' _ _ _ _ (hE _ _ β x).choose_spec (hE _ _ β' x').choose_spec
      (hE _ _ β x₁).choose_spec (hE _ _ β' x₁').choose_spec hx]
  loc i hi β β' x x' := (hS i hi β β' x x').1
  supp i hi β β' x x' := (hS i hi β β' x x').2
  int := hI
  mu_read i hi := (hM i hi).1
  mu_cls i hi k hk c := by
    have hJ : IsUnit (((gramN D k hk).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))).det) := by
      rw [← Hp.crd_orth k hk]
      have hu : IsUnit ((A.crd k hk).1 : Matrix (Fin (D.R.N k)) (Fin (D.R.N k)) D.host.E).det := by
        simpa [Matrix.GeneralLinearGroup.val_det_apply] using (Matrix.GeneralLinearGroup.det (A.crd k hk)).isUnit
      have hc : IsUnit (cT (sigD D : D.host.E →+* D.host.E) (A.crd k hk).1).det := by
        rw [cT, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
        exact hu.map _
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_mul]
      exact (hc.mul hu).map _
    obtain ⟨y, hy, hdet⟩ := exists_det_eq _ _ hJ _ ((St k hk).y c).2
    have hy' : y ∈ Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm := by
      show y ∈ UJ _ _
      rw [Matrix.map_one _ (map_zero _) (map_one _)]
      exact hy
    rw [← hdet, H.dt k hk c ⟨y, hy'⟩ hdet]
    exact muOf_det (i + 1) ⟨y, hy'⟩
  mu_mul i hi := (hM i hi).2.1
  mu_alg i hi := (hM i hi).2.2.1
  mu_unr i hi := (hM i hi).2.2.2.1
  mu_rat i hi := (hM i hi).2.2.2.2

theorem adLawOfTie_of_clauses (hE : UnderTie fun A _ a => PtEx A a) (hA : UnderTie fun A _ a => ∀ i hi, PtAway A a i hi)
    (hL : UnderTie fun A dtU a => ∀ i hi, LevAt A dtU a i hi) (hR : UnderTie fun A _ a => RatLaw A a) (hS : UnderTie fun A _ a => SizeLaw A a)
    (hM : UnderTie fun {_ _ _ _ _ _ _ _ _ t u μ _} _ dtU _ => MuLaw t u μ dtU)
    (hI : UnderTie fun {_ _ _ _ _ _ _ _ _ t u μ _} A _ a => ∀ i hi β β' x x' z, IntOff (t.O u μ).S (xiAd A a i hi β β' x x' z)) :
    AdLawOfTie := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a Hp H
  exact ⟨xiAd A a, muOf t u μ dtU, adLawAt_of_clauses Hp H (hE A dtU a Hp H) (hA A dtU a Hp H) (hL A dtU a Hp H)
    (hR A dtU a Hp H) (hS A dtU a Hp H) (hM A dtU a Hp H) (hI A dtU a Hp H)⟩

end GlobalTheory.TwV.Model

end
