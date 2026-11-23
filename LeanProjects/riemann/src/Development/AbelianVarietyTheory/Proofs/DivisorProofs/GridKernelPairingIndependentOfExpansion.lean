import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaAtOfVac
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetOpIdentityOfEntire
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseThetaKernelSeriesUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultilinearVanishOfProdVanishStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.FunObj.PairIndep

section Chain

variable {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]

theorem chainTo_congr (k k' : ∀ j, V j →ₗ[ℂ] V (j + 1)) : ∀ n, (∀ j < n, k j = k' j) → chainTo k n = chainTo k' n
  | 0, _ => rfl
  | n + 1, h => by
    show k n ∘ₗ chainTo k n = k' n ∘ₗ chainTo k' n
    rw [h n (Nat.lt_succ_self n), chainTo_congr k k' n fun j hj => h j (Nat.lt_succ_of_lt hj)]

theorem chainTo_add (k k' k'' : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ) (h : ∀ j, j ≠ j₀ → k' j = k j ∧ k'' j = k j)
    (h₀ : k'' j₀ = k j₀ + k' j₀) : ∀ n, j₀ < n → chainTo k'' n = chainTo k n + chainTo k' n
  | 0, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, hn => by
    show k'' n ∘ₗ chainTo k'' n = k n ∘ₗ chainTo k n + k' n ∘ₗ chainTo k' n
    rcases Nat.lt_succ_iff_lt_or_eq.1 hn with hlt | rfl
    · have hn' : n ≠ j₀ := Nat.ne_of_gt hlt
      rw [chainTo_add k k' k'' j₀ h h₀ n hlt, (h n hn').1, (h n hn').2, LinearMap.comp_add]
    · have e1 : chainTo k'' j₀ = chainTo k j₀ := chainTo_congr _ _ _ fun j hj => (h j (Nat.ne_of_lt hj)).2
      have e2 : chainTo k' j₀ = chainTo k j₀ := chainTo_congr _ _ _ fun j hj => (h j (Nat.ne_of_lt hj)).1
      rw [e1, e2, h₀, LinearMap.add_comp]

theorem chainTo_smul (k k' : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ) (c : ℂ) (h : ∀ j, j ≠ j₀ → k' j = k j)
    (h₀ : k' j₀ = c • k j₀) : ∀ n, j₀ < n → chainTo k' n = c • chainTo k n
  | 0, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, hn => by
    show k' n ∘ₗ chainTo k' n = c • (k n ∘ₗ chainTo k n)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hn with hlt | rfl
    · rw [chainTo_smul k k' j₀ c h h₀ n hlt, h n (Nat.ne_of_gt hlt), LinearMap.comp_smul]
    · rw [chainTo_congr k' k _ fun j hj => h j (Nat.ne_of_lt hj), h₀, LinearMap.smul_comp]

end Chain

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def thSub (W : G.Weil) (p : Pair T) : Submodule ℂ (WO (G.pS p) (G.pT p) → ℂ) where
  carrier := {g | IsThetaFunO W.ψ (G.pS p) (G.pT p) g}
  add_mem' := fun ha hb => GlobalTheory.OrientedHeis.theta_add ha hb
  zero_mem' := GlobalTheory.OrientedHeis.theta_zero
  smul_mem' := fun c _ hg => GlobalTheory.OrientedHeis.theta_smul c hg

theorem fockComp_lin (W : G.Weil) (B : VertexFrames G) (p : Pair T) (x : FinPt G p.small) (y : FinPt G p.big) (c : ℂ)
    {f g : WO (G.pS p) (G.pT p) → ℂ} (hf : IsThetaFunO W.ψ _ _ f) (hg : IsThetaFunO W.ψ _ _ g) :
    fockComp W B p (c • f + g) x y = c • fockComp W B p f x y + fockComp W B p g x y := by
  have ht : jetTab W B p (c • f + g) x y = c • jetTab W B p f x y + jetTab W B p g x y := by
    funext k
    simp only [jetTab, kerFin, fockIn, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [GlobalTheory.FockFiniteHeis.pureTensorO_lin _ _ _ _ W.ψ_std W.θ_is _ _ _ _ c hf hg]
    simp only [GridData.Weil.ker, thetaKO, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have := (GlobalTheory.JetIdentity.jetOpL (K := ℂ) (wt G p.small) (wt G p.big) (nuEnd G p)).map_add
    (c • jetTab W B p f x y) (jetTab W B p g x y)
  rw [LinearMap.map_smul] at this
  unfold fockComp
  rw [ht]
  exact this

theorem fockComp_zero (W : G.Weil) (B : VertexFrames G) (p : Pair T) (x : FinPt G p.small) (y : FinPt G p.big) :
    fockComp W B p 0 x y = 0 := by
  have := fockComp_lin W B p x y (-1) GlobalTheory.OrientedHeis.theta_zero GlobalTheory.OrientedHeis.theta_zero
  rwa [smul_zero, add_zero, neg_one_smul, neg_add_cancel] at this

def kLin (W : G.Weil) {U : Set T} {N : Std G U} (Z : Normal W N) (p : Pair T) (x : FinPt G p.small) (y : FinPt G p.big) :
    thSub W p →ₗ[ℂ] (VV ℂ (wt G p.small) →ₗ[ℂ] VV ℂ (wt G p.big)) where
  toFun g := Z.scal 1 p • fockComp W N.frC p g (x * N.u _) (y * N.u _)
  map_add' f g := by
    have := fockComp_lin W N.frC p (x * N.u _) (y * N.u _) 1 f.2 g.2
    rw [one_smul, one_smul] at this
    simp only [Submodule.coe_add, this, smul_add]
  map_smul' c f := by
    have := fockComp_lin W N.frC p (x * N.u _) (y * N.u _) c f.2 GlobalTheory.OrientedHeis.theta_zero
    rw [add_zero, fockComp_zero, add_zero] at this
    simp only [Submodule.coe_smul, this, RingHom.id_apply, smul_comm (Z.scal 1 p) c]

def tOp (W : G.Weil) {U : Set T} {N : Std G U} (Z : Normal W N) (p : Pair T) (e : AE D) :
    (WO (G.pS p) (G.pT p) → ℂ) →ₗ[ℂ] (WO (G.pS p) (G.pT p) → ℂ) :=
  Classical.epsilon (IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e
    (latO (G.pS p) (G.pT p) (N.latS p : Set _) (N.latT p : Set _) fun _ => True) 1 (Z.vac p))

theorem vec_eq_tOp {W : G.Weil} {U : Set T} {N : Std G U} (Z : Normal W N) {t : T} {p : Pair T} (hp : DefPair D.R.m p)
    {e : AE D} {d : FinDatum G t p} (he : d.e = e) (hz : d.z = 1) (hd : Z.HasVec d) :
    Z.vec d = tOp W Z p e d.fn ∧ tOp W Z p e d.fn ∈ thSub W p := by
  obtain ⟨f, hf⟩ := hd
  subst he
  have h1 : f = tOp W Z p d.e d.fn := hf.2 _ (Classical.epsilon_spec hf.1)
  have h2 : Z.vec d = f := by
    rw [Normal.vec, FinDatum.vec_eq W hf, hz]
    show W.om p 1 f = f
    rw [map_one]
    rfl
  exact ⟨h2.trans h1, h1 ▸ GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is hf (Z.vac_is p hp).2.theta⟩

variable (D) in

def pr (t : T) : Fin D.R.m ⊕ Fin D.R.m → Pair T := Sum.elim (fun j => .top t j) (fun i => .chi i D.R.m)

theorem pr_def (t : T) (k : Fin D.R.m ⊕ Fin D.R.m) : DefPair D.R.m (pr D t k) := by
  rcases k with j | i
  · exact j.2
  · exact ⟨i.2, rfl⟩

def intersection_update_fsHerm_neg_one {t : T} (d : PureDat G t) : ∀ k, FinDatum G t (pr D t k)
  | .inl j => d.1 j
  | .inr i => d.2 i

variable {W : G.Weil} {U : Set T}

def aSub (S : GridChoice W U) (t : T) (e : AE D) (k : Fin D.R.m ⊕ Fin D.R.m) :
    Submodule ℂ (WO (G.pS (pr D t k)) (G.pT (pr D t k)) → ℂ) :=
  (thSub W (pr D t k)).comap (tOp W S.Z (pr D t k) e)

def rOp (S : GridChoice W U) (t : T) (e : AE D) (k : Fin D.R.m ⊕ Fin D.R.m) : aSub S t e k →ₗ[ℂ] thSub W (pr D t k) :=
  LinearMap.codRestrict (thSub W (pr D t k)) ((tOp W S.Z (pr D t k) e).domRestrict (aSub S t e k)) fun g => g.2

def colK (S : GridChoice W U) (t : T) (e : AE D) (j : Fin D.R.m) (x : FinPt G (.top j)) (x' : FinPt G (.top (j + 1))) :
    aSub S t e (.inl j) →ₗ[ℂ] (VV ℂ (wt G (.top j)) →ₗ[ℂ] VV ℂ (wt G (.top (j + 1)))) :=
  (kLin W S.Z (pr D t (.inl j)) x x').comp (rOp S t e (.inl j))

def rowK (S : GridChoice W U) (t : T) (e : AE D) (i : Fin D.R.m) (y : FinPt G (.grid i D.R.m))
    (y' : FinPt G (.grid (i + 1) D.R.m)) :
    aSub S t e (.inr i) →ₗ[ℂ] (VV ℂ (wt G (.grid i D.R.m)) →ₗ[ℂ] VV ℂ (wt G (.grid (i + 1) D.R.m))) :=
  (kLin W S.Z (pr D t (.inr i)) y y').comp (rOp S t e (.inr i))

def colOf (S : GridChoice W U) (t : T) (e : AE D) (g : ∀ k, aSub S t e k) (x : ∀ j, FinPt G (.top j)) :
    VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (wt G (.top D.R.m)) :=
  chainTo (V := fun j => VV ℂ (wt G (.top j)))
    (fun j => if h : j < D.R.m then colK S t e ⟨j, h⟩ (x j) (x (j + 1)) (g (.inl ⟨j, h⟩)) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹

def rowOf (S : GridChoice W U) (t : T) (e : AE D) (g : ∀ k, aSub S t e k) (y : ∀ i, FinPt G (.grid i D.R.m)) :
    VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] VV ℂ (wt G (.grid D.R.m D.R.m)) :=
  chainTo (V := fun i => VV ℂ (wt G (.grid i D.R.m)))
    (fun i => if h : i < D.R.m then rowK S t e ⟨i, h⟩ (y i) (y (i + 1)) (g (.inr ⟨i, h⟩)) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.grid 0 D.R.m))⁻¹ ∘ₗ funOf (listedWt G (.grid 0 D.R.m))

section Upd

variable [DecidableEq (Fin D.R.m ⊕ Fin D.R.m)] (S : GridChoice W U) (t : T) (e : AE D) (g : ∀ k, aSub S t e k)

theorem colOf_inr (i₀ : Fin D.R.m) (v : aSub S t e (.inr i₀)) (x : ∀ j, FinPt G (.top j)) :
    colOf S t e (Function.update g (.inr i₀) v) x = colOf S t e g x := by
  unfold colOf
  refine congrArg (fun F => F ∘ₗ _) (chainTo_congr _ _ _ fun j _ => ?_)
  split_ifs with h
  all_goals (try rw [Function.update_of_ne (by simp)])

theorem rowOf_inl (j₀ : Fin D.R.m) (v : aSub S t e (.inl j₀)) (y : ∀ i, FinPt G (.grid i D.R.m)) :
    rowOf S t e (Function.update g (.inl j₀) v) y = rowOf S t e g y := by
  unfold rowOf
  refine congrArg (fun F => F ∘ₗ _) (chainTo_congr _ _ _ fun j _ => ?_)
  split_ifs with h
  all_goals (try rw [Function.update_of_ne (by simp)])

theorem colOf_add (j₀ : Fin D.R.m) (a b : aSub S t e (.inl j₀)) (x : ∀ j, FinPt G (.top j)) :
    colOf S t e (Function.update g (.inl j₀) (a + b)) x =
      colOf S t e (Function.update g (.inl j₀) a) x + colOf S t e (Function.update g (.inl j₀) b) x := by
  obtain ⟨j₀, hj₀⟩ := j₀
  unfold colOf
  rw [← LinearMap.add_comp]
  congr 1
  refine chainTo_add _ _ _ j₀ (fun j hj => ⟨?_, ?_⟩) ?_ D.R.m hj₀
  · split_ifs with h
    · have hne : (Sum.inl ⟨j, h⟩ : Fin D.R.m ⊕ Fin D.R.m) ≠ .inl ⟨j₀, hj₀⟩ := fun h' =>
        hj (congrArg Fin.val (Sum.inl_injective h'))
      rw [Function.update_of_ne hne, Function.update_of_ne hne]
    · rfl
  · split_ifs with h
    · have hne : (Sum.inl ⟨j, h⟩ : Fin D.R.m ⊕ Fin D.R.m) ≠ .inl ⟨j₀, hj₀⟩ := fun h' =>
        hj (congrArg Fin.val (Sum.inl_injective h'))
      rw [Function.update_of_ne hne, Function.update_of_ne hne]
    · rfl
  · rw [dif_pos hj₀, dif_pos hj₀, dif_pos hj₀, Function.update_self, Function.update_self, Function.update_self, map_add]

theorem colOf_smul (j₀ : Fin D.R.m) (c : ℂ) (a : aSub S t e (.inl j₀)) (x : ∀ j, FinPt G (.top j)) :
    colOf S t e (Function.update g (.inl j₀) (c • a)) x = c • colOf S t e (Function.update g (.inl j₀) a) x := by
  obtain ⟨j₀, hj₀⟩ := j₀
  unfold colOf
  rw [← LinearMap.smul_comp]
  congr 1
  refine chainTo_smul _ _ j₀ c (fun j hj => ?_) ?_ D.R.m hj₀
  · split_ifs with h
    · have hne : (Sum.inl ⟨j, h⟩ : Fin D.R.m ⊕ Fin D.R.m) ≠ .inl ⟨j₀, hj₀⟩ := fun h' =>
        hj (congrArg Fin.val (Sum.inl_injective h'))
      rw [Function.update_of_ne hne, Function.update_of_ne hne]
    · rfl
  · rw [dif_pos hj₀, dif_pos hj₀, Function.update_self, Function.update_self, map_smul]

theorem rowOf_add (i₀ : Fin D.R.m) (a b : aSub S t e (.inr i₀)) (y : ∀ i, FinPt G (.grid i D.R.m)) :
    rowOf S t e (Function.update g (.inr i₀) (a + b)) y =
      rowOf S t e (Function.update g (.inr i₀) a) y + rowOf S t e (Function.update g (.inr i₀) b) y := by
  obtain ⟨i₀, hi₀⟩ := i₀
  unfold rowOf
  rw [← LinearMap.add_comp]
  congr 1
  refine chainTo_add _ _ _ i₀ (fun j hj => ⟨?_, ?_⟩) ?_ D.R.m hi₀
  · split_ifs with h
    · have hne : (Sum.inr ⟨j, h⟩ : Fin D.R.m ⊕ Fin D.R.m) ≠ .inr ⟨i₀, hi₀⟩ := fun h' =>
        hj (congrArg Fin.val (Sum.inr_injective h'))
      rw [Function.update_of_ne hne, Function.update_of_ne hne]
    · rfl
  · split_ifs with h
    · have hne : (Sum.inr ⟨j, h⟩ : Fin D.R.m ⊕ Fin D.R.m) ≠ .inr ⟨i₀, hi₀⟩ := fun h' =>
        hj (congrArg Fin.val (Sum.inr_injective h'))
      rw [Function.update_of_ne hne, Function.update_of_ne hne]
    · rfl
  · rw [dif_pos hi₀, dif_pos hi₀, dif_pos hi₀, Function.update_self, Function.update_self, Function.update_self, map_add]

theorem rowOf_smul (i₀ : Fin D.R.m) (c : ℂ) (a : aSub S t e (.inr i₀)) (y : ∀ i, FinPt G (.grid i D.R.m)) :
    rowOf S t e (Function.update g (.inr i₀) (c • a)) y = c • rowOf S t e (Function.update g (.inr i₀) a) y := by
  obtain ⟨i₀, hi₀⟩ := i₀
  unfold rowOf
  rw [← LinearMap.smul_comp]
  congr 1
  refine chainTo_smul _ _ i₀ c (fun j hj => ?_) ?_ D.R.m hi₀
  · split_ifs with h
    · have hne : (Sum.inr ⟨j, h⟩ : Fin D.R.m ⊕ Fin D.R.m) ≠ .inr ⟨i₀, hi₀⟩ := fun h' =>
        hj (congrArg Fin.val (Sum.inr_injective h'))
      rw [Function.update_of_ne hne, Function.update_of_ne hne]
    · rfl
  · rw [dif_pos hi₀, dif_pos hi₀, Function.update_self, Function.update_self, map_smul]

end Upd

section Compl
variable {M N P Q : Type} [AddCommMonoid M] [Module ℂ M] [AddCommMonoid N] [Module ℂ N] [AddCommMonoid P] [Module ℂ P]
  [AddCommMonoid Q] [Module ℂ Q] (B : M →ₗ[ℂ] N →ₗ[ℂ] ℂ)

theorem compl₁₂_add_left (f f' : P →ₗ[ℂ] M) (g : Q →ₗ[ℂ] N) : B.compl₁₂ (f + f') g = B.compl₁₂ f g + B.compl₁₂ f' g := by
  ext u v
  simp [LinearMap.compl₁₂_apply]

theorem compl₁₂_add_right (f : P →ₗ[ℂ] M) (g g' : Q →ₗ[ℂ] N) : B.compl₁₂ f (g + g') = B.compl₁₂ f g + B.compl₁₂ f g' := by
  ext u v
  simp [LinearMap.compl₁₂_apply]

theorem compl₁₂_smul_left (c : ℂ) (f : P →ₗ[ℂ] M) (g : Q →ₗ[ℂ] N) : B.compl₁₂ (c • f) g = c • B.compl₁₂ f g := by
  ext u v
  simp [LinearMap.compl₁₂_apply]

theorem compl₁₂_smul_right (c : ℂ) (f : P →ₗ[ℂ] M) (g : Q →ₗ[ℂ] N) : B.compl₁₂ f (c • g) = c • B.compl₁₂ f g := by
  ext u v
  simp [LinearMap.compl₁₂_apply]

end Compl

def pairML (S : GridChoice W U) (t : T) (e : AE D) (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) :
    MultilinearMap ℂ (fun k => aSub S t e k)
      (VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] ℂ) where
  toFun g := (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))).compl₁₂
    (colOf S t e g x) (rowOf S t e g y)
  map_update_add' g k a b := by
    rcases k with j₀ | i₀
    · rw [colOf_add, rowOf_inl, rowOf_inl, rowOf_inl]
      exact compl₁₂_add_left _ _ _ _
    · rw [rowOf_add, colOf_inr, colOf_inr, colOf_inr]
      exact compl₁₂_add_right _ _ _ _
  map_update_smul' g k c a := by
    rcases k with j₀ | i₀
    · rw [colOf_smul, rowOf_inl, rowOf_inl]
      exact compl₁₂_smul_left _ _ _ _
    · rw [rowOf_smul, colOf_inr, colOf_inr]
      exact compl₁₂_smul_right _ _ _ _

open Classical in

def gd (S : GridChoice W U) (t : T) (e : AE D) (d : PureDat G t) (k : Fin D.R.m ⊕ Fin D.R.m) : aSub S t e k :=
  if h : (intersection_update_fsHerm_neg_one d k).fn ∈ aSub S t e k then ⟨(intersection_update_fsHerm_neg_one d k).fn, h⟩ else 0

theorem gd_coe {S : GridChoice W U} {t : T} {e : AE D} {d : PureDat G t} {k : Fin D.R.m ⊕ Fin D.R.m}
    (h : (intersection_update_fsHerm_neg_one d k).fn ∈ aSub S t e k) : ((gd S t e d k : aSub S t e k) : _ → ℂ) = (intersection_update_fsHerm_neg_one d k).fn := by
  rw [gd, dif_pos h]

theorem rOp_coe (S : GridChoice W U) (t : T) (e : AE D) (k : Fin D.R.m ⊕ Fin D.R.m) (g : aSub S t e k) :
    ((rOp S t e k g : thSub W (pr D t k)) : _ → ℂ) = tOp W S.Z (pr D t k) e g := rfl

theorem kkMap_eq_kLin {N : Std G U} (Z : Normal W N) {t : T} {p : Pair T} (d : FinDatum G t p) (x : FinPt G p.small)
    (y : FinPt G p.big) (v : thSub W p) (hv : (v : _ → ℂ) = Z.vec d) : Z.kkMap 1 d x y = kLin W Z p x y v := by
  show _ = Z.scal 1 p • fockComp W N.frC p v (x * N.u _) (y * N.u _)
  rw [hv]
  rfl

theorem colMap_eq (S : GridChoice W U) (t : T) (e : AE D) (d : PureDat G t)
    (h : ∀ k, S.Z.vec (intersection_update_fsHerm_neg_one d k) = tOp W S.Z (pr D t k) e (intersection_update_fsHerm_neg_one d k).fn ∧ (intersection_update_fsHerm_neg_one d k).fn ∈ aSub S t e k)
    (x : ∀ j, FinPt G (.top j)) : S.colMap d x = colOf S t e (gd S t e d) x := by
  unfold GridChoice.colMap colOf
  refine congrArg (fun F => F ∘ₗ _) (chainTo_congr _ _ _ fun j hj => ?_)
  rw [dif_pos hj, dif_pos hj]
  obtain ⟨h1, h2⟩ := h (.inl ⟨j, hj⟩)
  exact kkMap_eq_kLin S.Z (d.1 ⟨j, hj⟩) (x j) (x (j + 1)) (rOp S t e (.inl ⟨j, hj⟩) (gd S t e d (.inl ⟨j, hj⟩)))
    (by rw [rOp_coe, gd_coe h2]; exact h1.symm)

theorem rowMap_eq (S : GridChoice W U) (t : T) (e : AE D) (d : PureDat G t)
    (h : ∀ k, S.Z.vec (intersection_update_fsHerm_neg_one d k) = tOp W S.Z (pr D t k) e (intersection_update_fsHerm_neg_one d k).fn ∧ (intersection_update_fsHerm_neg_one d k).fn ∈ aSub S t e k)
    (y : ∀ i, FinPt G (.grid i D.R.m)) : S.rowMap d y = rowOf S t e (gd S t e d) y := by
  unfold GridChoice.rowMap rowOf
  refine congrArg (fun F => F ∘ₗ _) (chainTo_congr _ _ _ fun j hj => ?_)
  rw [dif_pos hj, dif_pos hj]
  obtain ⟨h1, h2⟩ := h (.inr ⟨j, hj⟩)
  exact kkMap_eq_kLin S.Z (d.2 ⟨j, hj⟩) (y j) (y (j + 1)) (rOp S t e (.inr ⟨j, hj⟩) (gd S t e d (.inr ⟨j, hj⟩)))
    (by rw [rOp_coe, gd_coe h2]; exact h1.symm)

end GlobalTheory.FunObj.PairIndep

open GlobalTheory.FunObj.PairIndep in

theorem GlobalTheory.FunObj.sumOK_vec_indep : ∀ (D : D7) (T : Type) (L : LevCh D T) (sc : GlobalTheory.ChiGrid.Consts) (G : GridData L sc) (W : G.Weil) (U : Set T) (S : GridChoice W U) (μ₀ : T), L.Is μ₀ → ∀ t ∈ U, ∀ Φ : G.Datum, (∀ β τ, S.IsExpansion t Φ β τ → ∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) ∧ ∀ β τ τ', S.IsExpansion t Φ β τ → S.IsExpansion t Φ β τ' → ∀ c : S.Classes t Φ β, S.pairAt τ c = S.pairAt τ' c := by
  intro D T L sc G W U S μ₀ hL t ht Φ
  have hv : ∀ (k : Fin D.R.m ⊕ Fin D.R.m) (d : FinDatum G t (pr D t k)), S.Z.HasVec d := fun k d =>
    hasVec G W μ₀ hL U S.N S.Z t ht _ (pr_def t k) d
  refine ⟨fun β τ _ d _ => ⟨fun j => hv (.inl j) (d.1 j), fun i => hv (.inr i) (d.2 i)⟩, fun β τ τ' hτ hτ' c => ?_⟩
  classical
  obtain ⟨e, he, hs, hx⟩ := hτ
  obtain ⟨e', he', hs', hx'⟩ := hτ'
  have hee : e' = e := GlobalTheory.BaseKernelUniq.idemSum_unique (G.V (.top 0)) he' he
  rw [hee] at hs' hx'
  have hposition : ∀ d ∈ τ.support ∪ τ'.support, ∀ k, (intersection_update_fsHerm_neg_one d k).e = e ∧ (intersection_update_fsHerm_neg_one d k).z = 1 := by
    intro d hd k
    rcases Finset.mem_union.1 hd with hd | hd
    · rcases k with j | i
      · exact ⟨((hs d hd).1 j).2.1, ((hs d hd).1 j).2.2⟩
      · exact ⟨((hs d hd).2 i).2.1, ((hs d hd).2 i).2.2⟩
    · rcases k with j | i
      · exact ⟨((hs' d hd).1 j).2.1, ((hs' d hd).1 j).2.2⟩
      · exact ⟨((hs' d hd).2 i).2.1, ((hs' d hd).2 i).2.2⟩
  have hk : ∀ d ∈ τ.support ∪ τ'.support, ∀ k,
      S.Z.vec (intersection_update_fsHerm_neg_one d k) = tOp W S.Z (pr D t k) e (intersection_update_fsHerm_neg_one d k).fn ∧ (intersection_update_fsHerm_neg_one d k).fn ∈ aSub S t e k :=
    fun d hd k => vec_eq_tOp S.Z (pr_def t k) (hposition d hd k).1 (hposition d hd k).2 (hv k _)
  have hP : ∀ τ₀ : PureDat G t →₀ ℂ, τ₀.support ⊆ τ.support ∪ τ'.support →
      S.pairAt τ₀ c = ∑ d ∈ τ.support ∪ τ'.support, τ₀ d • pairML S t e (S.ptTop c) (S.ptRow c) (gd S t e d) := by
    intro τ₀ hτ₀
    unfold GridChoice.pairAt
    rw [Finsupp.sum_of_support_subset τ₀ hτ₀]
    · refine Finset.sum_congr rfl fun d hd => congrArg (τ₀ d • ·) ?_
      rw [colMap_eq S t e d (hk d hd), rowMap_eq S t e d (hk d hd)]
      rfl
    · intro d _
      exact zero_smul _ _
  rw [hP τ Finset.subset_union_left, hP τ' Finset.subset_union_right, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  simp_rw [← sub_smul]
  refine GlobalTheory.T.sum_smul_multilinear_eq_zero_of_prod_vanish (aSub S t e) (pairML S t e (S.ptTop c) (S.ptRow c)) _ (fun d => τ d - τ' d) (gd S t e) fun x => ?_
  have hq : ∀ d ∈ τ.support ∪ τ'.support, ∏ k, ((gd S t e d k : aSub S t e k) : _ → ℂ) (x k) =
      (∏ j, (d.1 j).fn (x (.inl j))) * ∏ i, (d.2 i).fn (x (.inr i)) := by
    intro d hd
    rw [Fintype.prod_sum_type]
    congr 1
    · exact Finset.prod_congr rfl fun j _ => by rw [gd_coe (hk d hd _).2]; rfl
    · exact Finset.prod_congr rfl fun i _ => by rw [gd_coe (hk d hd _).2]; rfl
  rw [Finset.sum_congr rfl fun d hd => by rw [hq d hd]]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, sub_eq_zero]
  have hsum : ∀ τ₀ : PureDat G t →₀ ℂ, τ₀.support ⊆ τ.support ∪ τ'.support →
      ∑ d ∈ τ.support ∪ τ'.support, τ₀ d * ((∏ j, (d.1 j).fn (x (.inl j))) * ∏ i, (d.2 i).fn (x (.inr i))) =
        τ₀.sum fun d a => a * (∏ j, (d.1 j).fn (x (.inl j))) * ∏ i, (d.2 i).fn (x (.inr i)) := by
    intro τ₀ h
    rw [Finsupp.sum_of_support_subset τ₀ h]
    · simp only [mul_assoc]
    · intro d _
      rw [zero_mul, zero_mul]
  rw [hsum τ Finset.subset_union_left, hsum τ' Finset.subset_union_right]
  by_cases hh : (∀ j, IsHalf e (x (.inl j))) ∧ ∀ i, IsHalf e (x (.inr i))
  · exact (hx (fun j => x (.inl j)) (fun i => x (.inr i)) hh.1 hh.2).trans
      (hx' (fun j => x (.inl j)) (fun i => x (.inr i)) hh.1 hh.2).symm
  · have hz : ∀ d ∈ τ.support ∪ τ'.support,
        (∏ j, (d.1 j).fn (x (.inl j))) * ∏ i, (d.2 i).fn (x (.inr i)) = 0 := by
      intro d hd
      rcases not_and_or.1 hh with h1 | h1
      · obtain ⟨j, hj⟩ := not_forall.1 h1
        refine mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_univ j) ?_) _
        by_contra hne
        have := (d.1 j).sb.1 _ hne
        rw [show (d.1 j).e = e from (hposition d hd (.inl j)).1] at this
        exact hj this
      · obtain ⟨i, hi⟩ := not_forall.1 h1
        refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ i) ?_)
        by_contra hne
        have := (d.2 i).sb.1 _ hne
        rw [show (d.2 i).e = e from (hposition d hd (.inr i)).1] at this
        exact hi this
    have h0 : ∀ τ₀ : PureDat G t →₀ ℂ, τ₀.support ⊆ τ.support ∪ τ'.support →
        (τ₀.sum fun d a => a * (∏ j, (d.1 j).fn (x (.inl j))) * ∏ i, (d.2 i).fn (x (.inr i))) = 0 :=
      fun τ₀ h => Finset.sum_eq_zero fun d hd => by simp only [mul_assoc, hz d (h hd), mul_zero]
    rw [h0 τ Finset.subset_union_left, h0 τ' Finset.subset_union_right]
