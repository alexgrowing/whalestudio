import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmFockCompact

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.RowReal
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

theorem adaptedFrame_orthonormal {N r c N' : ℕ} (Γ : Matrix (Fin N) (Fin N) ℂ) (Γ' O : Matrix (Fin r) (Fin r) ℂ)
    (F : Matrix (Fin N) (Fin r) ℂ) (Zc : Matrix (Fin N) (Fin 1) ℂ) (hr : r = c) (hc : c + 1 = N') (hN : N = N')
    (hΓ : Γᴴ = Γ) (h1 : Fᴴ * Γ * F = Γ') (hO : Oᴴ * Γ' * O = 1) (h2 : Fᴴ * Γ * Zc = 0) (h3 : Zcᴴ * Γ * Zc = 1) :
    (Matrix.of (fun a k => Sum.elim (fun b : Fin c => (F * O) a (Fin.cast hr.symm b)) (fun _ : Fin 1 => Zc a 0)
      ((finSumFinEquiv.trans (finCongr hc)).symm (Fin.cast hN k))))ᴴ * Γ *
    Matrix.of (fun a k => Sum.elim (fun b : Fin c => (F * O) a (Fin.cast hr.symm b)) (fun _ : Fin 1 => Zc a 0)
      ((finSumFinEquiv.trans (finCongr hc)).symm (Fin.cast hN k))) = 1 := by
  subst hr hc hN
  set e := finSumFinEquiv (m := r) (n := 1)
  have hT : Matrix.of (fun a k => Sum.elim (fun b : Fin r => (F * O) a (Fin.cast rfl b)) (fun _ : Fin 1 => Zc a 0)
      ((e.trans (finCongr rfl)).symm (Fin.cast rfl k))) = (Matrix.fromCols (F * O) Zc).submatrix id e.symm := by
    ext a k
    simp only [Matrix.of_apply, Fin.cast_eq_self, Matrix.submatrix_apply, id]
    rcases h : e.symm k with b | b
    · simp [h, Matrix.fromCols]
    · simp [h, Matrix.fromCols, Subsingleton.elim b 0]
  have h4 : Zcᴴ * Γ * F = 0 := by
    have := congrArg Matrix.conjTranspose h2
    simpa [Matrix.conjTranspose_mul, hΓ, Matrix.mul_assoc] using this
  have a1 : ((Matrix.fromCols (F * O) Zc).submatrix id e.symm)ᴴ * Γ * (Matrix.fromCols (F * O) Zc).submatrix id e.symm =
      ((Matrix.fromCols (F * O) Zc)ᴴ * Γ * Matrix.fromCols (F * O) Zc).submatrix e.symm e.symm := rfl
  have b1 : (F * O)ᴴ * Γ * (F * O) = 1 := by
    rw [← hO, ← h1]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have b2 : (F * O)ᴴ * Γ * Zc = 0 := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Fᴴ, h2, Matrix.mul_zero]
  have b3 : Zcᴴ * Γ * (F * O) = 0 := by rw [← Matrix.mul_assoc, h4, Matrix.zero_mul]
  rw [hT, a1, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols,
    b1, b2, b3, h3, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem topFrame_orthonormal {μ0 : T} (hL : L.Is μ0) (W : G.Weil) (τ : D.what₂.Tau) :
    (topFrame W τ)ᴴ * gramAt D (G.V (.top D.R.m)) τ * topFrame W τ = 1 := by
  have hPt : PosOnb W (.top D.R.m) := posOnb_of_defNode W μ0 hL (X := .top D.R.m) le_rfl
  have hPg : PosOnb W (.grid D.R.m D.R.m) := posOnb_of_defNode W μ0 hL (X := .grid D.R.m D.R.m) ⟨le_rfl, rfl⟩
  have hm : ∀ {a b : ℕ} (X : Matrix (Fin (G.V (.top D.R.m)).rank) (Fin a) D.host.E)
      (Z : Matrix (Fin (G.V (.top D.R.m)).rank) (Fin b) D.host.E),
      (X.map (tauE D τ))ᴴ * gramAt D (G.V (.top D.R.m)) τ * Z.map (tauE D τ) =
        (Xᴴ * (G.V (.top D.R.m)).gram * Z).map (tauE D τ) := fun X Z => by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.conjTranspose_map _ (GlobalTheory.FockCompare.tauE_star τ)]; rfl
  have hΓ : (gramAt D (G.V (.top D.R.m)) τ)ᴴ = gramAt D (G.V (.top D.R.m)) τ := by
    have hB := hPt τ
    generalize W.onb (.top D.R.m) τ = B at hB
    generalize gramAt D (G.V (.top D.R.m)) τ = Γ at hB
    have hd : IsUnit B.det := Matrix.isUnit_det_of_left_inverse hB
    have h1 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
    have hG : Γ = (B⁻¹)ᴴ * B⁻¹ := by
      calc Γ = (B * B⁻¹)ᴴ * Γ * (B * B⁻¹) := by rw [h1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
        _ = (B⁻¹)ᴴ * (Bᴴ * Γ * B) * B⁻¹ := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [hB, Matrix.mul_one]
    rw [hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  refine adaptedFrame_orthonormal (c := (rowSizes D).nC D.R.m) _ (gramAt D (G.V (.grid D.R.m D.R.m)) τ) _ _ _
    (rank_gridM G (i := D.R.m) le_rfl) (rowSizes D).nC_succ (rank_top G (j := D.R.m) le_rfl) hΓ ?_ (hPg τ) ?_ ?_
  · exact (hm _ _).trans (congrArg (fun M => Matrix.map M (tauE D τ))
      (GlobalTheory.AutFunCounterexample.gram_pull (G.V (.top D.R.m)) (G.V (.grid D.R.m D.R.m)) G.sp.topDec.ι G.sp.topDec.isom))
  · refine (hm _ _).trans ((congrArg (fun M => Matrix.map M (tauE D τ)) G.sp.topDec.perp).trans ?_)
    ext i j; simp
  · refine (hm _ _).trans ((congrArg (fun M => Matrix.map M (tauE D τ)) G.sp.topDec.gram).trans ?_)
    ext i j
    obtain rfl := Subsingleton.elim i j
    simp [antiDiagonalSignGramMatrix]

theorem kappaTop_mul_topFrame {μ0 : T} (hL : L.Is μ0) (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) (τ : D.what₂.Tau) :
    compAt W.θ τ (mt _ (kappaTop W g)) * topFrame W τ = topFrame W τ *
      (embed (rowSizes D).nC_succ (g.2 (Fin.last D.R.m)) τ).1.submatrix
        (Fin.cast (rank_top G (j := D.R.m) le_rfl)) (Fin.cast (rank_top G (j := D.R.m) le_rfl)) := by
  have hPg : PosOnb W (.grid (Fin.last D.R.m : Fin (D.R.m + 1)) D.R.m) :=
    posOnb_of_defNode W μ0 hL (X := .grid (Fin.last D.R.m : Fin (D.R.m + 1)) D.R.m) ⟨Nat.lt_succ_iff.1 (Fin.last D.R.m).2, rfl⟩
  have hdO : IsUnit (W.onb (.grid D.R.m D.R.m) τ).det := Matrix.isUnit_det_of_left_inverse (hPg τ)
  have h1 : compAt W.θ τ (mt (G.V (.top D.R.m)) (kappaTop W g)) *
      (frameMat (G.V (.top D.R.m)) (G.V (.grid D.R.m D.R.m)) G.sp.topDec.ι).map (tauE D τ) =
      (frameMat (G.V (.top D.R.m)) (G.V (.grid D.R.m D.R.m)) G.sp.topDec.ι).map (tauE D τ) *
        compAt W.θ τ (mt (G.V (.grid D.R.m D.R.m)) ((kappa W g).2 (Fin.last D.R.m))) := (archM_kappaTop W g τ).1
  have h3 : compAt W.θ τ (mt (G.V (.top D.R.m)) (kappaTop W g)) * G.sp.topDec.a.map (tauE D τ) =
      G.sp.topDec.a.map (tauE D τ) := (archM_kappaTop W g τ).2
  have h2 : compAt W.θ τ (mt (G.V (.grid D.R.m D.R.m)) ((kappa W g).2 (Fin.last D.R.m))) =
      W.onb (.grid D.R.m D.R.m) τ * (g.2 (Fin.last D.R.m) τ).1.submatrix (Fin.cast (rank_gridM G (i := D.R.m) le_rfl))
        (Fin.cast (rank_gridM G (i := D.R.m) le_rfl)) * (W.onb (.grid D.R.m D.R.m) τ)⁻¹ :=
    compAt_kappa_snd g (Fin.last D.R.m) hPg τ
  exact mul_adaptedFrame_of_blocks (c := (rowSizes D).nC D.R.m) _ _ _ _ _
    ((g.2 (Fin.last D.R.m) τ).1 : Matrix (Fin ((rowSizes D).nC D.R.m)) (Fin ((rowSizes D).nC D.R.m)) ℂ)
    (rank_gridM G (i := D.R.m) le_rfl) (rowSizes D).nC_succ (rank_top G (j := D.R.m) le_rfl) hdO h1 h2 h3

theorem exists_unitary_change {a b : ℕ} (h : a = b) {Γ B F : Matrix (Fin a) (Fin a) ℂ} (hB : Bᴴ * Γ * B = 1)
    (hF : Fᴴ * Γ * F = 1) : ∃ c : Matrix.unitaryGroup (Fin b) ℂ, ∀ (A : Matrix (Fin a) (Fin a) ℂ) (v : Matrix.unitaryGroup (Fin b) ℂ),
      A * F = F * v.1.submatrix (Fin.cast h) (Fin.cast h) →
      A = B * (c * v * c⁻¹).1.submatrix (Fin.cast h) (Fin.cast h) * B⁻¹ := by
  subst h
  have hd : IsUnit B.det := Matrix.isUnit_det_of_left_inverse hB
  have hdF : IsUnit F.det := Matrix.isUnit_det_of_left_inverse hF
  have h1 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have hu : (B⁻¹ * F)ᴴ * (B⁻¹ * F) = 1 := by
    calc (B⁻¹ * F)ᴴ * (B⁻¹ * F) = (B⁻¹ * F)ᴴ * (Bᴴ * Γ * B) * (B⁻¹ * F) := by rw [hB, Matrix.mul_one]
      _ = Fᴴ * ((B * B⁻¹)ᴴ * Γ * (B * B⁻¹)) * F := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hF]
  have hu' : (B⁻¹ * F) * (B⁻¹ * F)ᴴ = 1 := mul_eq_one_comm.1 hu
  refine ⟨⟨B⁻¹ * F, Matrix.mem_unitaryGroup_iff'.2 hu⟩, fun A v hA => ?_⟩
  have hA' : A * F = F * v.1 := hA
  show A = B * (B⁻¹ * F * v.1 * (B⁻¹ * F)ᴴ) * B⁻¹
  calc A = A * (B * ((B⁻¹ * F) * (B⁻¹ * F)ᴴ) * B⁻¹) := by rw [hu', Matrix.mul_one, h1, Matrix.mul_one]
    _ = A * (B * B⁻¹) * F * (B⁻¹ * F)ᴴ * B⁻¹ := by simp only [Matrix.mul_assoc]
    _ = (B * B⁻¹) * (F * v.1) * (B⁻¹ * F)ᴴ * B⁻¹ := by rw [h1, Matrix.mul_one, Matrix.one_mul, hA']
    _ = _ := by simp only [Matrix.mul_assoc]

theorem exists_ptTop_conj {μ0 : T} (hL : L.Is μ0) (W : G.Weil) (n : Fin (D.R.m + 1)) :
    ∃ c : UG D.what₂.Tau ((rowSizes D).nR n), ∀ (g : Gc D.what₂.Tau (rowSizes D)) τ,
      compAt W.θ τ (mt _ (ptTop W g n)) = W.onb (.top n) τ *
        ((c * rowComp (rowSizes D) g n * c⁻¹) τ).1.submatrix (Fin.cast (rank_top G (Nat.lt_succ_iff.1 n.2)))
          (Fin.cast (rank_top G (Nat.lt_succ_iff.1 n.2))) * (W.onb (.top n) τ)⁻¹ := by
  have hP : PosOnb W (.top n) := posOnb_of_defNode W μ0 hL (X := .top n) (Nat.lt_succ_iff.1 n.2)
  by_cases h : (n : ℕ) = D.R.m
  · obtain rfl : n = Fin.last D.R.m := Fin.ext h
    choose c hc using fun τ => exists_unitary_change (rank_top G (j := D.R.m) le_rfl) (hP τ) (topFrame_orthonormal hL W τ)
    refine ⟨c, fun g τ => ?_⟩
    have hlast : rowComp (rowSizes D) g (Fin.last D.R.m) = embed (rowSizes D).nC_succ (g.2 (Fin.last D.R.m)) := by
      simp only [rowComp, MonoidHom.coe_mk, OneHom.coe_mk]
      exact Fin.snoc_last (α := fun j : Fin ((rowSizes D).m + 1) => UG D.what₂.Tau ((rowSizes D).nR j)) _ _
    rw [show ptTop W g ((Fin.last D.R.m : Fin (D.R.m + 1)) : ℕ) = kappaTop W g from ptTop_m W g]
    erw [hlast]
    exact hc τ _ _ (kappaTop_mul_topFrame hL W g τ)
  · refine ⟨1, fun g τ => ?_⟩
    rw [one_mul, inv_one, mul_one]
    exact eq_conj_of_inFrame (Matrix.isUnit_det_of_left_inverse (hP τ)) (GlobalTheory.T.compactChainTopRowRealPoint_inOrthonormalBasis hL W g n (fun e => absurd e h) τ)

def trColEquiv (G : GridData L sc) (j : Fin D.R.m) :
    PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank ≃ₗ[ℂ] Pol D.what₂.Tau ((rowSizes D).nR j) ((rowSizes D).nR (j + 1)) :=
  LinearEquiv.ofBijective (trCol G j).toLinearMap ⟨trCol_injective G j, MvPolynomial.rename_surjective _ fun y =>
    ⟨(y.1, Fin.cast (rank_top G (j := (j : ℕ) + 1) j.2).symm y.2.1, Fin.cast (rank_top G j.2.le).symm y.2.2), rfl⟩⟩

def trRowEquiv (G : GridData L sc) (i : Fin D.R.m) :
    PolF D (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank ≃ₗ[ℂ]
      Pol D.what₂.Tau ((rowSizes D).nC i) ((rowSizes D).nC (i + 1)) :=
  LinearEquiv.ofBijective (trRow G i).toLinearMap ⟨trRow_injective G i, MvPolynomial.rename_surjective _ fun y =>
    ⟨(y.1, Fin.cast (rank_gridM G i.2.le).symm y.2.2, Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2).symm y.2.1), rfl⟩⟩

def subEquiv {ι : Type} [Fintype ι] {a b : ℕ} (x : UG ι a × UG ι b) : Pol ι a b ≃ₗ[ℂ] Pol ι a b :=
  LinearEquiv.ofLinear (linSub (homMat a b x)) (linSub (homMat a b x⁻¹))
    (by rw [← Module.End.mul_eq_comp, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]; rfl)

theorem linSub_homMat_mul {ι : Type} [Fintype ι] {a b : ℕ} (x y : UG ι a × UG ι b) (p : Pol ι a b) :
    linSub (homMat a b x) (linSub (homMat a b y) p) = linSub (homMat a b (x * y)) p := by
  rw [map_mul, map_mul]; rfl

theorem om_fock_top_of_mat {μ0 : T} (hL : L.Is μ0) (W : G.Weil) {U : Set T} (S : GridChoice W U)
    (g : Gc D.what₂.Tau (rowSizes D)) (t : T) (j : Fin D.R.m)
    (u : UG D.what₂.Tau ((rowSizes D).nR j)) (v : UG D.what₂.Tau ((rowSizes D).nR (j + 1)))
    (c1 : ∀ τ, compAt W.θ τ (mt _ (ptTop W g j)) = W.onb (.top (j : ℕ)) τ *
      (u τ).1.submatrix (Fin.cast (rank_top G (j := j) j.2.le)) (Fin.cast (rank_top G (j := j) j.2.le)) *
      (W.onb (.top (j : ℕ)) τ)⁻¹)
    (c2 : ∀ τ, compAt W.θ τ (mt _ (ptTop W g ((j : ℕ) + 1))) = W.onb (.top ((j : ℕ) + 1)) τ *
      (v τ).1.submatrix (Fin.cast (rank_top G (j := (j : ℕ) + 1) j.2)) (Fin.cast (rank_top G (j := (j : ℕ) + 1) j.2)) *
      (W.onb (.top ((j : ℕ) + 1)) τ)⁻¹)
    (d : FinDatum G t (.top t j)) (hd : S.Z.HasVec d) (Q Q' : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank)
    (hQ : trCol G j Q' = rowScal (rowEntries D sc.cGap) j g • linSub (homMat _ _ (u, v)) (trCol G j Q)) :
    W.om (.top t j) (G.toPair (.top t j) (ptTop W g j) (ptTop W g (j + 1))) (W.fock (.top t j) (movedVec t S d) Q) =
      W.fock (.top t j) (movedVec t S d) Q' := by
  have hX : DefNode D.R.m (.top (j : ℕ)) := j.2.le
  have hY : DefNode D.R.m (.top ((j : ℕ) + 1)) := j.2
  have hp : DefPair D.R.m (Pair.top t (j : ℕ)) := j.2
  obtain ⟨hf, hv⟩ := GlobalTheory.T.movedVector_definitePair_theta_fockVacuum W S t (.top t j) hp d hd
  have hc := GlobalTheory.T.compactChain_topPair_movedVector_rowCharacter hL W S g t j d hd
  have key := GlobalTheory.T.weil_compactRealPoint_fockVector_substitution W (.top t j) j.2 (fun _ => (G.V (.top (j : ℕ))).rank) (fun _ => (G.V (.top ((j : ℕ) + 1))).rank)
    (fun _ => le_rfl) (fun _ => le_rfl) (fun ρ => (GlobalTheory.T.definiteNode_cartan_orthonormalBasis_allPlaces hL W _ hX ρ).1) (fun ρ => (GlobalTheory.T.definiteNode_cartan_orthonormalBasis_allPlaces hL W _ hY ρ).1)
    (fun ρ => (GlobalTheory.T.definiteNode_cartan_orthonormalBasis_allPlaces hL W _ hX ρ).2.1) (fun ρ => (GlobalTheory.T.definiteNode_cartan_orthonormalBasis_allPlaces hL W _ hY ρ).2.1) _ hf hv
    (fun τ => (u τ).1.submatrix (Fin.cast (rank_top G (j := j) j.2.le)) (Fin.cast (rank_top G (j := j) j.2.le)))
    (fun τ => (v τ).1.submatrix (Fin.cast (rank_top G (j := (j : ℕ) + 1) j.2)) (Fin.cast (rank_top G (j := (j : ℕ) + 1) j.2)))
    (fun ρ => isKMat_cast _ _ (Or.inl rfl)) (fun ρ => isKMat_cast _ _ (Or.inl rfl))
    (ptTop W g j) (ptTop W g (j + 1)) (ptTop_mem W g _) (ptTop_mem W g _) c1 c2 _ hc Q
  have hQ' : Q' = rowScal (rowEntries D sc.cGap) j g • fockSubAll (fun _ => (G.V (.top (j : ℕ))).rank)
      (fun _ => (G.V (.top ((j : ℕ) + 1))).rank)
      (fun τ => (u τ).1.submatrix (Fin.cast (rank_top G (j := j) j.2.le)) (Fin.cast (rank_top G (j := j) j.2.le)))
      (fun τ => (v τ).1.submatrix (Fin.cast (rank_top G (j := (j : ℕ) + 1) j.2)) (Fin.cast (rank_top G (j := (j : ℕ) + 1) j.2)))
      Q := by
    apply trCol_injective G j
    rw [hQ, map_smul, GlobalTheory.T.fockSubstitution_rowStep_rename_unitary G j u v Q]
  show W.om (.top t j) (ptTop W g j, ptTop W g (j + 1)) _ = _
  rw [key, hQ', LinearMap.map_smul]

theorem exists_fock_transport : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T} (hL : L.Is μ0)
    (W : G.Weil), ∃ (tc : ∀ j : Fin D.R.m, PolF D (G.V (.top ((j : ℕ) + 1))).rank (G.V (.top j)).rank ≃ₗ[ℂ]
        Pol D.what₂.Tau ((rowSizes D).nR (j.castSucc : Fin ((rowSizes D).m + 1))) ((rowSizes D).nR (j.succ : Fin ((rowSizes D).m + 1))))
      (tr : ∀ i : Fin D.R.m, PolF D (G.V (.grid i D.R.m)).rank (G.V (.grid ((i : ℕ) + 1) D.R.m)).rank ≃ₗ[ℂ]
        Pol D.what₂.Tau ((rowSizes D).nC (i.castSucc : Fin ((rowSizes D).m + 1))) ((rowSizes D).nC (i.succ : Fin ((rowSizes D).m + 1)))),
      ∀ {U : Set T} (S : GridChoice W U) (g : Gc D.what₂.Tau (rowSizes D)) (t : T),
        (∀ (j : Fin D.R.m) (d : FinDatum G t (.top t j)), S.Z.HasVec d → ∀ Q,
          W.om (.top t j) (G.toPair (.top t j) (ptTop W g j) (ptTop W g (j + 1))) (W.fock (.top t j) (movedVec t S d) Q) =
            W.fock (.top t j) (movedVec t S d) ((tc j).symm (rowFock (rowEntries D sc.cGap) j g (tc j Q)))) ∧
        (∀ (i : Fin D.R.m) (d : FinDatum G t (.chi i D.R.m)), S.Z.HasVec d → ∀ Q,
          W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) (ptGrid W g i) (ptGrid W g (i + 1)))
              (W.fock (.chi i D.R.m) (movedVec t S d) Q) =
            W.fock (.chi i D.R.m) (movedVec t S d) ((tr i).symm (colFock (rowEntries D sc.cGap) i g (tr i Q)))) := by
  intro D T L sc G μ0 hL W
  choose c hc using exists_ptTop_conj hL W
  refine ⟨fun j => (trColEquiv G j).trans (subEquiv (c j.castSucc, c j.succ)).symm, fun i => trRowEquiv G i,
    fun S g t => ⟨fun j d hd Q => ?_, fun i d hd Q => ?_⟩⟩
  · refine om_fock_top_of_mat hL W S g t j _ _ (hc j.castSucc g) (hc j.succ g) d hd Q _ ?_
    have e : ∀ y, trCol G j ((trColEquiv G j).symm y) = y := fun y => (trColEquiv G j).apply_symm_apply y
    refine (e _).trans ?_
    show linSub (homMat _ _ (c j.castSucc, c j.succ)) (rowScal (rowEntries D sc.cGap) j g •
      linSub (homMat _ _ (rowComp (rowSizes D) g j.castSucc, rowComp (rowSizes D) g j.succ))
        (linSub (homMat _ _ (c j.castSucc, c j.succ)⁻¹) (trCol G j Q))) = _
    rw [LinearMap.map_smul, linSub_homMat_mul, linSub_homMat_mul]
    rfl
  · exact om_fock_chi hL W S g t i d hd Q _ ((trRowEquiv G i).apply_symm_apply _)

end GlobalTheory.RowReal
