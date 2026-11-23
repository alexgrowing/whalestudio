import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KeepSideBMtVPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideBTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.YsOfFi
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelGroupWithCharacterAtTypePlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.LevelRechar

open ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.LevGChar

section Loc
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {R : Type} [CommRing R]
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))}

open Classical in

def dU (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* R)
    (r : ℕ) (x : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) : Rˣ :=
  if h : IsUnit (red (NX.intLift v (NX.detT r x))) then h.unit else 1

theorem isUnit_red (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* R) (r : ℕ)
    (x : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) (hdx : Valued.v (NX.detT r x) = 1) :
    IsUnit (red (NX.intLift v (NX.detT r x))) := by
  have hix : NX.detT r x ∈ v.adicCompletionIntegers (maximalRealSubfield L) := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hdx]
  have ex : NX.intLift v (NX.detT r x) = ⟨_, hix⟩ := by rw [NX.intLift, dif_pos hix]
  rw [ex]; exact (isUnit_int hdx hix).map red

theorem dU_eq (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* R) (r : ℕ)
    (x : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L)))
    (h : IsUnit (red (NX.intLift v (NX.detT r x)))) : dU v red r x = h.unit := by
  unfold dU
  rw [dif_pos h]

theorem dU_mul (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* R)
    (hred : ∀ z : v.adicCompletionIntegers (maximalRealSubfield L),
      Valued.v (z : v.adicCompletion (maximalRealSubfield L)) < 1 → red z = 0) (r : ℕ)
    (x y : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L)))
    (hx : NX.InParah v r x) (hy : NX.InParah v r y)
    (hdx : Valued.v (NX.detT r x) = 1) (hdy : Valued.v (NX.detT r y) = 1) :
    dU v red r (x * y) = dU v red r x * dU v red r y := by
  have hix : NX.detT r x ∈ v.adicCompletionIntegers (maximalRealSubfield L) := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hdx]
  have hiy : NX.detT r y ∈ v.adicCompletionIntegers (maximalRealSubfield L) := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hdy]
  have ex : NX.intLift v (NX.detT r x) = ⟨_, hix⟩ := by rw [NX.intLift, dif_pos hix]
  have ey : NX.intLift v (NX.detT r y) = ⟨_, hiy⟩ := by rw [NX.intLift, dif_pos hiy]
  have hxy : red (NX.intLift v (NX.detT r (x * y))) =
      red (NX.intLift v (NX.detT r x)) * red (NX.intLift v (NX.detT r y)) := by
    rw [ex, ey, ← map_mul]
    exact red_intLift red hred _ (by simpa using i_detT_mul v r x y hx hy)
  have hux := isUnit_red red r x hdx
  have huy := isUnit_red red r y hdy
  have huxy : IsUnit (red (NX.intLift v (NX.detT r (x * y)))) := by rw [hxy]; exact hux.mul huy
  rw [dU_eq red r _ hux, dU_eq red r _ huy, dU_eq red r _ huxy]
  exact Units.ext (by simp [hxy])

theorem dU_one (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* R)
    (hred : ∀ z : v.adicCompletionIntegers (maximalRealSubfield L),
      Valued.v (z : v.adicCompletion (maximalRealSubfield L)) < 1 → red z = 0) (r : ℕ)
    (x : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L)))
    (hx : ∀ a b, Valued.v (x a b - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) a b) < 1) :
    dU v red r x = 1 := by
  have hd : red (NX.intLift v (NX.detT r x)) = 1 := by
    rw [red_intLift red hred 1 (by simpa using i_detT_cong v r x hx), map_one]
  have hu : IsUnit (red (NX.intLift v (NX.detT r x))) := by rw [hd]; exact isUnit_one
  rw [dU_eq red r x hu]
  exact Units.ext (by rw [IsUnit.unit_spec, hd]; rfl)

theorem exists_cong {ι : Type} [Fintype ι] (s : ι → SplitPlace L) : ∃ N : ℕ, 0 < N ∧ ∀ κ : GAf L n, NG.Cong L n N κ →
    ∀ t a b, Valued.v (NX.locM (s t) κ a b -
      (1 : Matrix (Fin n) (Fin n) ((s t).v.adicCompletion (maximalRealSubfield L))) a b) < 1 := by
  have hpos : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)), 0 < Ideal.absNorm v.asIdeal := fun v =>
    Nat.pos_of_ne_zero fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have hmem : ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (N : ℕ), Ideal.absNorm v.asIdeal ∣ N →
      (N : 𝓞 (maximalRealSubfield L)) ∈ v.asIdeal := fun v N h =>
    Ideal.mem_of_dvd _ (Nat.cast_dvd_cast h) (Ideal.absNorm_mem _)
  refine ⟨∏ t, Ideal.absNorm (s t).v.asIdeal, Finset.prod_pos fun _ _ => hpos _, fun κ hκ t => ?_⟩
  have hd : Ideal.absNorm (s t).v.asIdeal ∣ ∏ t, Ideal.absNorm (s t).v.asIdeal :=
    Finset.dvd_prod_of_mem (fun t => Ideal.absNorm (s t).v.asIdeal) (Finset.mem_univ t)
  exact locM_cong (s t) (hmem _ _ hd) κ hκ

end Loc

theorem mul_ringHom_units_ratio {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (p : B) (a a' : Aˣ) :
    p * f (a' : A) = p * f (a : A) * f ((a' * a⁻¹ : Aˣ) : A) := by
  rw [mul_assoc, ← map_mul, ← Units.val_mul, mul_comm a', mul_inv_cancel_left]

theorem exists_mul_hom {G H : Type} [Group G] [CommGroup H] {J : Subgroup G} (χ : J →* H) (c : G → H)
    (hc : ∀ κ κ' : J, c ((κ * κ' : J) : G) = c κ * c κ') : ∃ χ' : J →* H, ∀ κ : J, χ' κ = χ κ * c κ :=
  ⟨MonoidHom.mk' (fun κ => χ κ * c κ) (fun κ κ' => by rw [hc, map_mul, mul_mul_mul_comm]), fun _ => rfl⟩

theorem gVal_rechar (D : D7) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (kv : Σ k : Fin 2, D.nd.PlG k) (s : SplitPlace D.host.E)
    (red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1))
    (τ τ' : (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (x : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E)))
    (hu : IsUnit (red (NX.intLift s.v (NX.detT D.R.r x)))) :
    NX.gVal D i k b kv s red τ' x = NX.gVal D i k b kv s red τ x *
      NX.toKk D i k (((τ' (dU s.v red D.R.r x) * (τ (dU s.v red D.R.r x))⁻¹ : (FractionRing (D.ntw.O i))ˣ)) :
        FractionRing (D.ntw.O i)) := by
  unfold NX.gVal
  rw [dif_pos hu, dif_pos hu, dU_eq red _ x hu]
  exact mul_ringHom_units_ratio _ _ _ _

theorem exists_rechar : ∀ (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀] (ρ₀ : Representation (FractionRing (D.ntw.O i)) (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) W₀) (τ τ' : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) (M : NX.MtVReal D i j b k Q ψ e W₀ ρ₀ τ), ∃ χ' : M.J →* (NX.Kk D i k)ˣ, (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : κ ∈ M.J, χ' ⟨κ, h⟩ = 1) ∧ NX.HypOutsideF M.J χ' (NX.badV D i Q) ∧ ∀ κ (h : κ ∈ M.J), ((χ' ⟨κ, h⟩ : (NX.Kk D i k)ˣ) : NX.Kk D i k) = (∏ kv : (Σ kk : Fin 2, D.nd.PlG kk), NX.gVal D i k b kv (M.sp (NX.pG D kv)) (M.redG kv) (τ' kv) (NX.locM (M.sp (NX.pG D kv)) κ)) * (∏ P ∈ M.QP, NX.ofOk D i k (NX.tameVal ψ P e (NX.resRep (M.sp P) P (NX.detT D.R.r (NX.locM (M.sp P) κ)))).1) * (∏ P ∈ M.DP, NX.ofO0 D i k (NX.tameVal (D.ntw.delta i) P (if b then e else -e) (NX.resRep (M.sp P) P (NX.detT D.R.r (NX.locM (M.sp P) κ)))).1) := by
  intro D i j b k Q ψ e W₀ _ _ ρ₀ τ τ' M
  classical
  have hred : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk),
      ∀ z : (M.sp (NX.pG D kv)).v.adicCompletionIntegers (maximalRealSubfield D.host.E),
      Valued.v (z : (M.sp (NX.pG D kv)).v.adicCompletion (maximalRealSubfield D.host.E)) < 1 → M.redG kv z = 0 := by
    intro kv z hz
    haveI : Fact (D.host.g kv.1).Prime := ⟨D.host.g_prime kv.1⟩
    exact i_red_zero _ (M.redG kv) z hz
  have hdet : ∀ (s : SplitPlace D.host.E) (κ : GAf D.host.E D.R.nV), κ ∈ Umax D.host.E D.R.nV →
      NX.InParah s.v D.R.r (NX.locM s κ) → Valued.v (NX.detT D.R.r (NX.locM s κ)) = 1 := fun s κ hU hp =>
    i_detT_one _ _ _ (NX.locM s κ⁻¹) (by rw [← locM_mul, mul_inv_cancel, locM_one]) (locM_int s (inv_mem hU)) hp
  obtain ⟨c, hc⟩ : ∃ c : GAf D.host.E D.R.nV → (NX.Kk D i k)ˣ, ∀ κ, c κ =
      ∏ kv : (Σ kk : Fin 2, D.nd.PlG kk), Units.map (NX.toKk D i k).toMonoidHom
        (τ' kv (dU (M.sp (NX.pG D kv)).v (M.redG kv) D.R.r (NX.locM (M.sp (NX.pG D kv)) κ)) *
          (τ kv (dU (M.sp (NX.pG D kv)).v (M.redG kv) D.R.r (NX.locM (M.sp (NX.pG D kv)) κ)))⁻¹) := ⟨_, fun _ => rfl⟩
  have hmul : ∀ κ κ' : M.J, c ((κ * κ' : M.J) : GAf D.host.E D.R.nV) = c κ * c κ' := by
    rintro ⟨κ, hκ⟩ ⟨κ', hκ'⟩
    obtain ⟨h1, h2, -⟩ := (M.J_mem κ).1 hκ
    obtain ⟨h1', h2', -⟩ := (M.J_mem κ').1 hκ'
    show c (κ * κ') = c κ * c κ'
    rw [hc, hc, hc, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun kv _ => ?_
    rw [locM_mul, dU_mul _ (hred kv) _ _ _ (h2 kv).1 (h2' kv).1 (hdet _ _ h1 (h2 kv).1) (hdet _ _ h1' (h2' kv).1),
      ← MonoidHom.map_mul, map_mul (τ kv), map_mul (τ' kv), mul_inv, mul_mul_mul_comm]
  have hone : ∀ κ : GAf D.host.E D.R.nV,
      (∀ kv a b, Valued.v (NX.locM (M.sp (NX.pG D kv)) κ a b - (1 : Matrix (Fin D.R.nV) (Fin D.R.nV)
        ((M.sp (NX.pG D kv)).v.adicCompletion (maximalRealSubfield D.host.E))) a b) < 1) → c κ = 1 := by
    intro κ hg
    rw [hc]
    refine Finset.prod_eq_one fun kv _ => ?_
    rw [dU_one _ (hred kv) _ _ (hg kv), map_one, map_one, inv_one, mul_one, map_one]
  obtain ⟨χ', hχ'⟩ := exists_mul_hom M.χ c hmul
  have hχ : ∀ κ (h : κ ∈ M.J), χ' ⟨κ, h⟩ = M.χ ⟨κ, h⟩ * c κ := fun κ h => hχ' ⟨κ, h⟩
  refine ⟨χ', ?_, ?_, ?_⟩
  · obtain ⟨N, hN, hJ⟩ := M.J_open
    obtain ⟨N', hN', hc'⟩ := exists_cong (n := D.R.nV)
      (fun kv : (Σ kk : Fin 2, D.nd.PlG kk) => M.sp (NX.pG D kv))
    refine ⟨N * N', Nat.mul_pos hN hN', fun κ hκ => ?_⟩
    obtain ⟨h, h1⟩ := hJ κ hκ.of_mul_left
    refine ⟨h, ?_⟩
    have h2 : c κ = 1 := hone κ (hc' κ hκ.of_mul_right)
    rw [hχ, h1, h2, one_mul]
  · intro κ hκ
    refine ⟨(M.hyp κ hκ).1, fun h => ?_⟩
    rw [hχ, (M.hyp κ hκ).2 h, one_mul]
    refine hone κ fun kv a b => ?_
    have hw := (M.sp (NX.pG D kv)).w_under
    rw [M.sp_w _ (Or.inr (Or.inr ⟨kv, rfl⟩))] at hw
    have hb : (M.sp (NX.pG D kv)).v ∈ NX.badV D i Q :=
      ⟨NX.pG D kv, hw, Or.inr (Or.inl ⟨kv.1, D.naut.plGw_over kv.1 kv.2⟩)⟩
    rw [locM_triv _ hκ hb]
    simp
  · intro κ h
    obtain ⟨h1, h2, -⟩ := (M.J_mem κ).1 h
    rw [hχ, Units.val_mul, M.chi_eq κ h, hc, Units.coe_prod,
      Finset.prod_congr rfl fun kv _ => gVal_rechar D i k b kv (M.sp (NX.pG D kv)) (M.redG kv) (τ kv) (τ' kv) _
        (isUnit_red _ _ _ (hdet _ _ h1 (h2 kv).1)), Finset.prod_mul_distrib]
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    ring

end GlobalTheory.LevelRechar
