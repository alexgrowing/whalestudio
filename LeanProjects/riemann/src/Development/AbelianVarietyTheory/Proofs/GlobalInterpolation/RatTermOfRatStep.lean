import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BelowFiniteNonempty
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SubstitutionAdjoint
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HomConjEquivMemHomAt

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.KerT

noncomputable section

namespace GlobalTheory.KerRat

section Gen

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

theorem phiT_move {a b : ℕ} {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E a ST SG) (d' : Deco E b ST SG')
    (γ : Sp E a ≃ₗ[E] Sp E a) (γ' : Sp E b ≃ₗ[E] Sp E b) (h : GLG E a SG) (h' : GLG E b SG') (x : HomE E a b) :
    phiT K (d.act γ h) (d'.act γ' h') (γ'.toLinearMap ∘ₗ x ∘ₗ γ.symm.toLinearMap) = phiT K d d' x := by
  unfold phiT
  refine @if_congr _ _ _ (_) (_) _ _ _ _ (forall_congr' fun Q => ?_) rfl rfl
  have key : ∀ y, (y ∈ (d.act γ h).at Q.1 → (γ'.toLinearMap ∘ₗ x ∘ₗ γ.symm.toLinearMap) y ∈ (d'.act γ' h').at Q.1 ∧
      (d'.act γ' h').f Q ((γ'.toLinearMap ∘ₗ x ∘ₗ γ.symm.toLinearMap) y) = (d.act γ h).f Q y) ↔
      (γ.symm y ∈ d.at Q.1 → x (γ.symm y) ∈ d'.at Q.1 ∧ d'.f Q (x (γ.symm y)) = d.f Q (γ.symm y)) := fun y => by
    show (y ∈ localization₂ _ (gmap γ d.N) → γ' (x (γ.symm y)) ∈ localization₂ _ (gmap γ' d'.N) ∧
      d'.f Q (γ'.symm (γ' (x (γ.symm y)))) = d.f Q (γ.symm y)) ↔ _
    rw [mem_localization_gmap, mem_localization_gmap, LinearEquiv.symm_apply_apply]
  refine ⟨fun H y => ?_, fun H y => (key y).2 (H _)⟩
  have := (key (γ y)).1 (H _)
  rwa [LinearEquiv.symm_apply_apply] at this

theorem kerOf_move {a b : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 E))} {V V' : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] (th : ThDist E K a b SB V V') (Sa : Finset (HeightOneSpectrum (𝓞 E))) (cA cB : ℕ)
    (rho : UF E a →* Module.End K V) (rho' : UF E b →* Module.End K V') (γ : UF E a) (γ' : UF E b)
    (N : Submodule (𝓞 E) (Sp E a)) (fr fr₂ : Frs E a SB) (N' : Submodule (𝓞 E) (Sp E b)) (fr' fr₂' : Frs E b SB)
    (Ξ Ξ₂ : HomE E a b → K)
    (hcong : ∀ x x', x - x' ∈ mulLat cB (homAt Sa N N') → th N fr N' fr' cB x = th N fr N' fr' cB x')
    (heq : ∀ x, th (gmap γ.1 N) fr₂ (gmap γ'.1 N') fr₂' cB (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) =
      (rho' γ') ∘ₗ (th N fr N' fr' cB x) ∘ₗ (rho γ⁻¹))
    (hΞ : ∀ x z, z ∈ mulLat cB (homAt Sa N N') → Ξ (x + z) = Ξ x)
    (hΞ₂ : ∀ x : HomE E a b, Ξ₂ (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) = Ξ x) :
    kerOf th Sa cA cB (gmap γ.1 N) fr₂ (gmap γ'.1 N') fr₂' Ξ₂ =
      (rho' γ') ∘ₗ kerOf th Sa cA cB N fr N' fr' Ξ ∘ₗ (rho γ⁻¹) := by
  have hm : ∀ (g : UF E a), rho g ∘ₗ rho g⁻¹ = LinearMap.id := fun g => by
    rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl
  have hm' : ∀ (g : UF E b), rho' g ∘ₗ rho' g⁻¹ = LinearMap.id := fun g => by
    rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl
  let φ : (V →ₗ[K] V') ≃+ (V →ₗ[K] V') :=
    { toFun := fun L => rho' γ' ∘ₗ L ∘ₗ rho γ⁻¹
      invFun := fun L => rho' γ'⁻¹ ∘ₗ L ∘ₗ rho γ
      left_inv := fun L => by
        have h1 := hm γ⁻¹
        have h2 := hm' γ'⁻¹
        rw [inv_inv] at h1 h2
        show rho' γ'⁻¹ ∘ₗ (rho' γ' ∘ₗ L ∘ₗ rho γ⁻¹) ∘ₗ rho γ = L
        rw [LinearMap.comp_assoc, LinearMap.comp_assoc, h1, ← LinearMap.comp_assoc, h2]; simp
      right_inv := fun L => by
        show rho' γ' ∘ₗ (rho' γ'⁻¹ ∘ₗ L ∘ₗ rho γ) ∘ₗ rho γ⁻¹ = L
        rw [LinearMap.comp_assoc, LinearMap.comp_assoc, hm, ← LinearMap.comp_assoc, hm']; simp
      map_add' := fun L L' => by simp [LinearMap.comp_add, LinearMap.add_comp] }
  have hH := homConjEquiv_mem_homAt Sa γ.1 γ'.1 N N'
  unfold kerOf
  rw [latSum_transport_equiv (homConjEquiv γ.1 γ'.1) (divLat cA (homAt Sa N N')) (mulLat cB (homAt Sa N N')) _ _
    (mem_divLat_equiv_iff _ _ _ hH cA) (mem_mulLat_equiv_iff _ _ _ hH cB)
    (fun x => φ (Ξ x • th N fr N' fr' cB x))]
  · show _ = φ _
    unfold latSum
    rw [φ.map_finsum]
  · intro x x' hx
    have h1 : Ξ x = Ξ x' := by
      have := hΞ x' (x - x') hx
      rwa [add_sub_cancel] at this
    rw [h1, hcong x x' hx]
  · intro x
    show Ξ₂ (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) • th _ _ _ _ cB (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap)
      = rho' γ' ∘ₗ (Ξ x • th N fr N' fr' cB x) ∘ₗ rho γ⁻¹
    rw [heq, hΞ₂, LinearMap.smul_comp, LinearMap.comp_smul]

omit [NumberField E] [StarRing E] in
theorem mulLat_le_divLat {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (c D : ℕ) (M : Submodule (𝓞 E) H) :
    mulLat c M ≤ divLat D M := by
  rintro _ ⟨y, hy, rfl⟩
  show (D : 𝓞 E) • ((c : 𝓞 E) • y) ∈ M
  exact M.smul_mem _ (M.smul_mem _ hy)

end Gen

theorem thDistC_class {X : Fields} (A : Amb X) {a b : ℕ} (Sa SB : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K)
    (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (fr : Frs X.E a SB) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (fr' : Frs X.E b SB) (c : ℕ)
    (x x' : HomE X.E a b) (h : x - x' ∈ mulLat c (homAt Sa N N')) :
    thDistC A Sa SB D sel mU mI lam lam' n N fr N' fr' c x = thDistC A Sa SB D sel mU mI lam lam' n N fr N' fr' c x' := by
  have hL : A.IsLift Sa N N' c x = A.IsLift Sa N N' c x' := by
    funext s
    unfold Amb.IsLift
    have : s - x ∈ mulLat c (homAt Sa N N') ↔ s - x' ∈ mulLat c (homAt Sa N N') := by
      rw [show s - x' = (s - x) + (x - x') by abel]
      exact (Submodule.add_mem_iff_left _ h).symm
    rw [this]
  have hW : A.liftW Sa N N' c x = A.liftW Sa N N' c x' := by unfold Amb.liftW; rw [hL]
  have hT : A.thInd Sa N N' c x = A.thInd Sa N N' c x' := by unfold Amb.thInd; rw [hW]
  have hJ : A.jetK Sa N N' c x = A.jetK Sa N N' c x' := by funext m; unfold Amb.jetK; rw [hT]
  have hD : x ∈ divLat D (homAt Sa N N') ↔ x' ∈ divLat D (homAt Sa N N') := by
    rw [show x = x' + (x - x') by abel]
    exact Submodule.add_mem_iff_left _ (mulLat_le_divLat c D _ h)
  unfold thDistC
  rw [hJ]
  exact @if_congr _ _ _ (_) (_) _ _ _ _ (and_congr_right fun _ => hD) rfl rfl

theorem ratTerm_of_ratStep : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (A : Amb X) (u : Pr.Word) (i : ℕ), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → RatStep W Ch sel mu cst A u i (i + 1) → RatTerm W Ch sel mu cst A u i (i + 1) := by
  classical
  intro X Pr R W Ch sel S mu cst A u i _ hPr _ _ hR SG SG' d fr d' fr' Ξ₀ γ γ' hbox
  have hB : 0 < cBof sel mu cst u := by
    unfold cBof
    refine Nat.mul_pos (hPr.T_prime u).pos (pow_pos (Finset.prod_pos fun P _ => ?_) _)
    exact Nat.pos_of_ne_zero (by unfold Formalism.L2.Col.qOf; rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.1.ne_bot)
  unfold term ker
  refine kerOf_move (stepT W Ch sel mu cst A u i (W.lamTrue u (i + 1))) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u)
    ((rhoVr X.emb (W.lamTrue u i)).comp (ufGL X.E (R.N i)))
    ((rhoVr X.emb (W.lamTrue u (i + 1))).comp (ufGL X.E (R.N (i + 1)))) γ γ' d.1.N fr (fun P => γ.1 * fr P) d'.1.N fr' (fun P => γ'.1 * fr' P)
    (fun x => phiT X.K d.1 d'.1 x * Ξ₀ x)
    (fun x => phiT X.K (d.1.act γ.1 1) (d'.1.act γ'.1 1) x * Ξ₀ (γ'.1.symm.toLinearMap ∘ₗ x ∘ₗ γ.1.toLinearMap)) ?_ ?_ ?_ ?_
  · intro x x' h
    exact thDistC_class A _ _ _ _ _ _ _ _ _ _ _ _ _ _ x x' h
  · intro x
    by_cases hx : x ∈ divLat (cAof sel mu cst * cBof sel mu cst u) (homAt (Sall sel mu u) d.1.N d'.1.N)
    · exact hR γ γ' d.1.N fr d'.1.N fr' _ x ⟨⟨d.2.lat, d.2.uni⟩, ⟨d'.2.lat, d'.2.uni⟩, hB, Dvd.intro_left _ rfl, hx⟩
    · have hx2 := mt (mem_divLat_equiv_iff _ _ _ (homConjEquiv_mem_homAt (Sall sel mu u) γ.1 γ'.1 d.1.N d'.1.N)
        (cAof sel mu cst * cBof sel mu cst u) x).1 hx
      unfold stepT thDistC
      rw [if_neg fun h => hx2 h.2, if_neg fun h => hx h.2, LinearMap.zero_comp, LinearMap.comp_zero]
  · rintro x _ ⟨y₀, hy₀, rfl⟩
    refine congrArg₂ (· * ·) ?_ ?_
    · refine GlobalTheory.TopInv.phiT_add _ _ d'.2 x y₀ _ (fun P => ?_) fun P v hv => hy₀ P.1 (Finset.mem_union_left _ P.2) v hv
      have h1 : Pr.piT u ∈ P.1.asIdeal := by
        have h := P.2
        unfold Primes.vT divs at h
        split_ifs at h with hf
        · simpa using h
        · simp at h
      rw [cBof, Nat.cast_mul, ← hPr.piT_norm]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h1)
    · exact hbox.2 x _ ⟨y₀, fun P hP => hy₀ P (Finset.mem_union_right _ hP), rfl⟩
  · intro x
    refine congrArg₂ (· * ·) (phiT_move d.1 d'.1 γ.1 γ'.1 1 1 x) (congrArg Ξ₀ ?_)
    ext y l
    simp

end GlobalTheory.KerRat
