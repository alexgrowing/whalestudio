import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemRange

noncomputable section

open WittVector Ideal Matrix CategoryTheory Function

namespace GlobalTheory.DieudonneSandwich

open GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta

section Linear

theorem equivFun_semilinear {R S X Y n m : Type*} [CommRing R] [CommRing S] [AddCommGroup X]
    [Module R X] [AddCommGroup Y] [Module S Y] [Fintype n] [Fintype m] {σ : R →+* S}
    (f : X →ₛₗ[σ] Y) (bx : Module.Basis n R X) (bz : Module.Basis m S Y) (x : X) :
    bz.equivFun (f x) = (Matrix.of fun i j => bz.repr (f (bx j)) i) *ᵥ (σ ∘ bx.equivFun x) := by
  have h1 : f x = ∑ j, σ (bx.repr x j) • f (bx j) := by
    conv_lhs => rw [← bx.sum_repr x, map_sum]
    simp only [map_smulₛₗ]
  funext i
  rw [h1]
  simp [Matrix.mulVec, dotProduct, mul_comm]

theorem exists_basis_reduction {A O M D n : Type*} [CommRing A] [CommRing O] [AddCommGroup M]
    [Module A M] [AddCommGroup D] [Module O D] [Fintype n] {θ : A →+* O} (hθ : Surjective θ)
    {ξ : A} (hξ : θ ξ = 0) (r : M →ₛₗ[θ] D) (hr : Surjective r)
    (hk : ∀ m, r m = 0 → ∃ n, m = ξ • n) (b : Module.Basis n A M) :
    ∃ c : Module.Basis n O D, ∀ m, c.equivFun (r m) = θ ∘ b.equivFun m := by
  classical
  have li : LinearIndependent O fun i => r (b i) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose a ha using fun i => hθ (g i)
    obtain ⟨n, hn⟩ := hk (∑ i, a i • b i) (by simpa [map_sum, map_smulₛₗ, ha] using hg)
    have := congrArg (fun m => θ (b.repr m i)) hn
    simpa [Finsupp.single_apply, apply_ite θ, ha, hξ] using this
  have sp : ⊤ ≤ Submodule.span O (Set.range fun i => r (b i)) := by
    intro y _
    obtain ⟨m, rfl⟩ := hr y
    rw [← b.sum_repr m, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨Module.Basis.mk li sp, fun m => ?_⟩
  rw [equivFun_semilinear r b]
  have : (Matrix.of fun i j => (Module.Basis.mk li sp).repr (r (b j)) i) = 1 := by
    ext i j
    have := (Module.Basis.mk li sp).repr_self_apply j i
    rw [Module.Basis.mk_apply] at this
    rw [Matrix.of_apply, this, Matrix.one_apply]
    simp only [eq_comm]
  rw [this, Matrix.one_mulVec]

theorem exists_unit_of_generator {O X : Type*} [CommRing O] [AddCommGroup X] [Module O X]
    (e : O ≃ₗ[O] X) (x : X) (hx : ∀ y, ∃ c : O, y = c • x) : ∃ u : Oˣ, x = (u : O) • e 1 := by
  obtain ⟨a, rfl⟩ := e.surjective x
  obtain ⟨c, hc⟩ := hx (e 1)
  rw [← map_smul, e.injective.eq_iff, smul_eq_mul] at hc
  refine ⟨(IsUnit.of_mul_eq_one_right c hc.symm).unit, ?_⟩
  rw [IsUnit.unit_spec, ← map_smul, smul_eq_mul, mul_one]

theorem reduction_generates {A O M D : Type*} [CommRing A] [CommRing O] [AddCommGroup M]
    [Module A M] [AddCommGroup D] [Module O D] {θ : A →+* O} (r : M →ₛₗ[θ] D)
    (e : M ≃ₗ[A] A) (m : M) : r m = θ (e m) • r (e.symm 1) := by
  rw [← map_smulₛₗ]
  congr 1
  exact e.injective (by simp)

end Linear

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

theorem form_map_smul (M : PDivGroup p O ⥤ ModuleCat.{0} (Ainf p O)) [M.Additive]
    {G G' : PDivGroup p O} (l : M.obj G' →ₗ[Ainf p O] Ainf p O) (m : M.obj G) (a : ℤ_[p])
    (f : G ⟶ G') : l (M.map (a • f) m) = ofPadic p O a * l (M.map f m) := by
  haveI : IsAdicComplete (span {(p : Ainf p O)}) (Ainf p O) := WittVector.isAdicCompleteIdealSpanP
  let T : (G ⟶ G') →+ Ainf p O :=
    AddMonoidHom.mk' (fun f => l (M.map f m)) fun f g => by
      rw [M.map_add, ← map_add]; rfl
  exact Dieudonne.map_padic_smul (ofPadic p O) T a f

def tateToM (M : PDivGroup p O ⥤ ModuleCat.{0} (Ainf p O)) [M.Additive] {G : PDivGroup p O}
    {h : ℕ} (b : Module.Basis (Fin h) (Ainf p O) (M.obj G)) (m₀ : M.obj (const p O)) :
    G.Tate →ₛₗ[ofPadic p O] M.obj G where
  toFun t := M.map (constHom G t) m₀
  map_add' s t := by rw [map_add, M.map_add]; rfl
  map_smul' a t := b.ext_elem fun i => by
    rw [map_smul, map_smul]
    exact form_map_smul M (b.coord i) m₀ a _

def endMap (M : PDivGroup p O ⥤ ModuleCat.{0} (Ainf p O)) [M.Additive] (G : PDivGroup p O) :
    End G →+* Module.End (Ainf p O) (M.obj G) where
  toFun f := (M.map f).hom
  map_one' := congrArg ModuleCat.Hom.hom (M.map_id G)
  map_mul' f g := congrArg ModuleCat.Hom.hom (M.map_comp g f)
  map_zero' := congrArg ModuleCat.Hom.hom (M.map_zero G G)
  map_add' f g := congrArg ModuleCat.Hom.hom (M.map_add (f := f) (g := g))

theorem exists_dual_basis [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε)
    {G : PDivGroup p O} (hG : Bijective (pairing G O).flip) {h : ℕ}
    (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) :
    ∃ χ : Fin h → G.dual.Tate, (∀ i t, pairing G O t (χ i) = e t i • epsTate hε) ∧
      ∀ χ', χ' = ∑ i, epsPairing hε G (e.symm (Pi.single i 1)) χ' • χ i := by
  choose χ hχ using fun i : Fin h => hG.2
    (LinearMap.toSpanSingleton ℤ_[p] _ (epsTate hε) ∘ₗ LinearMap.proj i ∘ₗ e.toLinearMap)
  have h1 : ∀ i t, pairing G O t (χ i) = e t i • epsTate hε := fun i t =>
    LinearMap.congr_fun (hχ i) t
  refine ⟨χ, h1, fun χ' => hG.1 (LinearMap.ext fun t => ?_)⟩
  have ht : t = ∑ i, e t i • e.symm (Pi.single i 1) := by
    apply e.injective
    rw [map_sum]
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  change pairing G O t χ' = pairing G O t _
  rw [map_sum]
  conv_lhs => rw [ht, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, h1, LinearMap.smul_apply, ← epsPairing_smul hε, smul_comm]

theorem exists_equiv_constDlogT :
    ∃ e : O ≃ₗ[O] (const p O).dual.omega, e 1 = constDlogT p O := by
  have hb : Bijective (omegaMap _ (PDivGroup.mu p O) (PDivGroup.mu p O).bidual.inv) :=
    bijective_iff_has_inverse.2 ⟨omegaMap _ _ (PDivGroup.mu p O).bidual.hom,
      fun x => by rw [← LinearMap.comp_apply, ← omegaMap_comp, Iso.hom_inv_id, omegaMap_id]; rfl,
      fun x => by rw [← LinearMap.comp_apply, ← omegaMap_comp, Iso.inv_hom_id, omegaMap_id]; rfl⟩
  refine ⟨muOmegaEquiv p O ≪≫ₗ LinearEquiv.ofBijective _ hb, ?_⟩
  exact congrArg (omegaMap _ (PDivGroup.mu p O) (PDivGroup.mu p O).bidual.inv) (one_smul O _)

theorem exists_equiv_muLieGen :
    ∃ e : O ≃ₗ[O] (PDivGroup.mu p O).Lie, e 1 = muLieGen p O :=
  ⟨(LinearMap.ringLmapEquivSelf O O O).symm ≪≫ₗ (muOmegaEquiv p O).symm.dualMap,
    LinearMap.ext fun w => by simp [muLieGen]⟩

theorem sandwichAt_of_covariant {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} [Algebra O C] (hv : v.Integers O) [IsDomain O] {ε : PreTilt O p}
    (hε : IsPrimitiveSystem ε) (hcov : CovariantDieudonneAt ε) : HodgeTateSandwichAt hε := by
  classical
  have hε1 : IsPrimitiveRoot (root ε).untilt p := by simpa [zeta] using hε 1
  obtain ⟨hdom, -, hker, hsurj, hnu, -, -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε1
  have hxi : fontaineTheta O p (xi ε) = 0 := by
    rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self _
  haveI : IsIntegrallyClosedIn O C := isIntegrallyClosedIn_iff.2
    ⟨hv.hom_inj, fun hx => hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.1 hx)⟩
  obtain ⟨M, H, ψ, r, ι, π, hadd, hM, hψ, nψ, hr, nr, hex, nι, nπ, -, e₀, e₁, u, he₀, -, hu⟩ := hcov

  obtain ⟨u₁, hu₁⟩ : ∃ u₁ : Oˣ, r _ (e₀.symm 1) = (u₁ : O) • ι _ (constDlogT p O) := by
    obtain ⟨e, he⟩ := exists_equiv_constDlogT (p := p) (O := O)
    have hb : Bijective (ι (const p O)) :=
      ⟨(hex _).1, fun y => ((hex _).2.1 y).1 (Subsingleton.elim _ _)⟩
    rw [← he]
    refine exists_unit_of_generator (e ≪≫ₗ LinearEquiv.ofBijective _ hb) _ fun y => ?_
    obtain ⟨m, rfl⟩ := (hr _).1 y
    exact ⟨_, reduction_generates _ e₀ m⟩
  obtain ⟨u₂, hu₂⟩ : ∃ u₂ : Oˣ, π _ (r _ (e₁.symm 1)) = (u₂ : O) • muLieGen p O := by
    obtain ⟨e, he⟩ := exists_equiv_muLieGen (p := p) (O := O)
    rw [← he]
    refine exists_unit_of_generator e _ fun y => ?_
    obtain ⟨z, rfl⟩ := (hex _).2.2 y
    obtain ⟨m, rfl⟩ := (hr _).1 z
    exact ⟨_, by rw [reduction_generates _ e₁ m, map_smul]⟩
  refine ⟨u₁, Units.map (padicToO p O : ℤ_[p] →* O) u⁻¹ * u₂⁻¹, fun G Λ _ _ ρ => ?_⟩
  haveI := (hM G).1
  haveI := (hM G).2.1
  haveI := G.finite_tate C
  haveI := G.free_tate C
  let b := Module.finBasisOfFinrankEq (Ainf p O) (M.obj G) (hM G).2.2
  let tb := Module.finBasisOfFinrankEq ℤ_[p] G.Tate (G.finrank_tate C)
  let e := tb.equivFun
  obtain ⟨χ, hχ, hχ'⟩ := exists_dual_basis hε (G.pairing_flip_bijective C) e
  obtain ⟨c, hc⟩ := exists_basis_reduction hsurj hxi (r G) (hr G).1 (fun m => ((hr G).2 m).1) b
  choose n hn using (hψ G).2
  let Φ := tateToM M b (e₀.symm 1)
  have hΦ : ∀ t, Φ t = M.map (constHom G t) (e₀.symm 1) := fun _ => rfl
  let F : Matrix (Fin G.height) (Fin G.height) (Ainf p O) :=
    Matrix.of fun i j => b.repr (Φ (tb j)) i
  have hF : ∀ t, F *ᵥ (ofPadic p O ∘ e t) = b.equivFun (Φ t) := fun t =>
    (equivFun_semilinear Φ tb b t).symm
  let Gm : Matrix (Fin G.height) (Fin G.height) (Ainf p O) :=
    Matrix.of fun i k => ofPadic p O ↑u⁻¹ * e₁ (M.map (charHom G (χ i)) (b k))
  have hG : ∀ m i, (Gm *ᵥ b.equivFun m) i =
      ofPadic p O ↑u⁻¹ * e₁ (M.map (charHom G (χ i)) m) := fun m i => by
    conv_rhs => rw [← b.sum_repr m, map_sum, map_sum, Finset.mul_sum]
    simp only [Gm, Matrix.mulVec, dotProduct, Matrix.of_apply, map_smul, smul_eq_mul,
      Module.Basis.equivFun_apply]
    exact Finset.sum_congr rfl fun k _ => by ring
  let Ψ : Matrix (Fin G.height) (Fin G.height) (Ainf p O) :=
    Matrix.of fun i k => b.repr (ψ G (b k)) i
  have hΨ : ∀ m, Ψ *ᵥ (phiInv p O ∘ b.equivFun m) = b.equivFun (ψ G m) := fun m =>
    (equivFun_semilinear (ψ G) b b m).symm
  let ρT : Λ →ₐ[ℤ_[p]] Matrix (Fin G.height) (Fin G.height) ℤ_[p] :=
    (LinearMap.toMatrixAlgEquiv tb).toAlgHom.comp (ρ.onTateAlg O)
  have hρT : ∀ a t, ρT a *ᵥ e t = e (tateMap G G O (ρ a) t) := fun a t =>
    LinearMap.toMatrix_mulVec_repr tb tb _ t
  let ρM : Λ →+* Matrix (Fin G.height) (Fin G.height) (Ainf p O) :=
    (LinearMap.toMatrixAlgEquiv b).toAlgHom.toRingHom.comp ((endMap M G).comp ρ)
  have hρM : ∀ a m, ρM a *ᵥ b.equivFun m = b.equivFun (M.map (ρ a) m) := fun a m =>
    LinearMap.toMatrix_mulVec_repr b b _ m
  have hGF : ∀ t i, (Gm *ᵥ b.equivFun (Φ t)) i = ofPadic p O (e t i) * Sandwich.mu ε := by
    intro t i
    have h1 : M.map (charHom G (χ i)) (Φ t) =
        M.map (e t i • epsHom (zeta ε) hε.zeta_zero (zeta_succ_pow ε)) (e₀.symm 1) := by
      rw [hΦ, ← ModuleCat.comp_apply, ← M.map_comp, constHom_comp_charHom, hχ, map_smul]
      rfl
    have h2 := form_map_smul M e₁.toLinearMap (e₀.symm 1) (e t i)
      (epsHom (zeta ε) hε.zeta_zero (zeta_succ_pow ε))
    have h3 : ofPadic p O ↑u⁻¹ * ofPadic p O u = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    rw [LinearEquiv.coe_coe, hu (zeta ε) _ _ (fun _ => rfl), LinearEquiv.apply_symm_apply] at h2
    rw [hG, h1, h2]
    linear_combination (ofPadic p O (e t i) * Sandwich.mu ε) * h3
  let D : Datum ε G.height Λ :=
    { F := F, G := Gm, Ψ := Ψ
      Ψ' := Matrix.of fun i k => phiInv p O (b.repr (n (b k)) i)
      ρT := ρT, ρM := ρM
      G_mul_F := by
        ext1 i j
        refine (hGF (tb j) i).trans ?_
        by_cases hij : i = j
        · simp [e, hij]
        · simp [e, hij, Finsupp.single_apply, Ne.symm hij]
      F_eq := by
        ext1 i j
        refine Eq.trans ?_ (congrFun (hΨ (Φ (tb j))) i).symm
        have h0 : ψ _ (e₀.symm 1) = e₀.symm 1 := e₀.injective (by rw [he₀]; simp)
        rw [hΦ, ← nψ, h0]
        rfl
      Ψ_mul := by
        ext1 i j
        refine (congrFun (hΨ (n (b j))) i).trans ?_
        rw [hn]
        simp [Matrix.one_apply, Finsupp.single_apply, eq_comm]
      F_act := fun a => by
        ext1 i j
        refine Eq.trans ?_ (congrFun (hρM a (Φ (tb j))) i).symm
        rw [hΦ, ← ModuleCat.comp_apply, ← M.map_comp, ← constHom_tateMap, ← hΦ, ← hF, ← hρT]
        simp [e, Matrix.mul_apply, Matrix.mulVec, dotProduct, Finsupp.single_apply] }
  have red : ∀ (X : Matrix (Fin G.height) (Fin G.height) (Ainf p O)) (y : Fin G.height → Ainf p O),
      Matrix.toLin' (X.map (fontaineTheta O p)) (fontaineTheta O p ∘ y) =
        fontaineTheta O p ∘ (X *ᵥ y) := fun X y =>
    funext fun i => (RingHom.map_mulVec _ X y i).symm
  have hal : ∀ t, D.al (toO e t) = (u₁ : O) • c.equivFun (ι G (hodgeTate G t)) := fun t => by
    refine (red F (ofPadic p O ∘ e t)).trans ?_
    rw [hF, ← hc, hΦ, ← nr, hu₁, map_smul, map_smul, nι, hodgeTate_eq_omegaDualMap]
  have hact : ∀ a y, actH D a (c.equivFun y) = c.equivFun (H.map (ρ a) y) := fun a y => by
    obtain ⟨m, rfl⟩ := (hr G).1 y
    rw [nr, hc, hc, ← hρM]
    exact red _ _
  have hbb : ∀ y i, D.bb (c.equivFun y) i =
      padicToO p O ↑u⁻¹ * ↑u₂⁻¹ * π G y (dlog G (χ i)) := fun y i => by
    obtain ⟨m, rfl⟩ := (hr G).1 y
    have h1 := nπ _ _ (charHom G (χ i)) (r G m)
    rw [nr, reduction_generates _ e₁, map_smul, hu₂, lieMap_charHom] at h1
    have h2 := LinearMap.congr_fun h1 (dlogT p O)
    simp only [LinearMap.smul_apply, muLieGen_dlogT, smul_eq_mul, mul_one] at h2
    rw [hc]
    refine (congrFun (red Gm _) i).trans ?_
    rw [Function.comp_apply, hG, map_mul, ← h2, mul_assoc, mul_comm _ (u₂ : O),
      Units.inv_mul_cancel_left]
    rfl

  have hFil : ∀ y, c.equivFun y ∈ D.Fil ↔ π G y = 0 := fun y => by
    refine ⟨fun hy => ?_, fun hy => funext fun i => by rw [hbb, hy]; simp⟩
    have hr' : ∀ x, π G (c.equivFun.symm (D.al x)) = 0 := fun x => by
      have hx : x = ∑ j, x j • toO e (tb j) := by
        funext i
        simp [toO, e, Finset.sum_apply, Finsupp.single_apply, apply_ite (padicToO p O)]
      rw [hx, map_sum, map_sum, map_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_smul, hal, map_smul, map_smul, map_smul, map_smul, LinearEquiv.symm_apply_apply,
        (hex G).2.1.apply_apply_eq_zero, smul_zero, smul_zero]
    obtain ⟨x, hx⟩ := (GlobalTheory.Sandwich.HodgeTateBound.bound p C v O hv ε hε1 Λ _ D).2.2.2.1 _ hy
    have h1 := hr' x
    rw [hx, map_smul, LinearEquiv.symm_apply_apply, map_smul] at h1
    exact LinearMap.ext fun w =>
      (mul_eq_zero.1 (LinearMap.congr_fun h1 w)).resolve_left hnu
  let fil₀ : G.dual.omega →ₗ[O] D.Fil := (c.equivFun.toLinearMap ∘ₗ ι G).codRestrict _ fun w =>
    (hFil _).2 ((hex G).2.1.apply_apply_eq_zero w)
  have hfil : Bijective fil₀ := by
    refine ⟨fun w w' h => (hex G).1 (c.equivFun.injective (congrArg Subtype.val h)), fun x => ?_⟩
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, rfl⟩ := c.equivFun.surjective x
    obtain ⟨w, rfl⟩ := ((hex G).2.1 y).1 ((hFil y).1 hx)
    exact ⟨w, rfl⟩
  have hk : D.Fil = LinearMap.ker (π G ∘ₗ c.equivFun.symm.toLinearMap) := by
    ext x
    obtain ⟨y, rfl⟩ := c.equivFun.surjective x
    rw [hFil, LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
  let lie := Submodule.quotEquivOfEq _ _ hk ≪≫ₗ LinearMap.quotKerEquivOfSurjective
    (π G ∘ₗ c.equivFun.symm.toLinearMap) ((hex G).2.2.comp c.equivFun.symm.surjective)
  have hlie : ∀ y, lie (D.Fil.mkQ (c.equivFun y)) = π G y := fun y =>
    congrArg (π G) (c.equivFun.symm_apply_apply y)
  refine ⟨D, e, LinearEquiv.ofBijective fil₀ hfil, lie, fun a t => (hρT a t).symm,
    fun a w => ?_, fun a m => ?_, fun t => ?_, fun x χ' => ?_⟩
  · exact (congrArg c.equivFun (nι _ _ (ρ a) w).symm).trans (hact a _).symm
  · obtain ⟨y, rfl⟩ := c.equivFun.surjective m
    rw [hact, hlie, hlie]
    exact nπ _ _ (ρ a) y
  · rw [hal, hodgeTate_eq_omegaMap]
    rfl
  · obtain ⟨y, rfl⟩ := (hex G).2.2 x
    rw [← dlog_eq_omegaMap]
    conv_lhs => rw [← hlie, LinearEquiv.symm_apply_apply]
    conv_rhs => rw [hχ' χ', map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dlog_smul (padicToO p O), map_smul, smul_eq_mul]
    have : bQuot D (D.Fil.mkQ (c.equivFun y)) i = _ := hbb y i
    rw [this]
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe]
    ring

theorem hodgeTateSandwich_of_prismaticDieudonne₂ : GlobalTheory.Published.PrismaticDieudonneHodge →
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
      (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
      [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ [IsDomain O] (ε : PreTilt O p)
      (hε : IsPrimitiveSystem ε), HodgeTateSandwichAt hε :=
  fun h p _ C _ _ _ v O _ _ _ _ hv _ ε hε =>
    sandwichAt_of_covariant hv hε
      (h.covariant p C v O hv ε (by simpa [zeta] using hε 1))

end GlobalTheory.DieudonneSandwich
