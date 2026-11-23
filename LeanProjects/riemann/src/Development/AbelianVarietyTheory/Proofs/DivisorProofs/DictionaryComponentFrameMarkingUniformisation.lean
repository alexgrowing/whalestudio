import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueLinearLiftUniformisedFibres
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0CompLinear
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitFrameEqOrthonormalMulTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RealAdelesCmFieldEquivComplexCmType
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArchimedeanMatrixUnitaryContinuousMultiplicativeStatement
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.OrthonormalBaseFrameNeg

namespace GlobalTheory.AdTh.MarkUniq

section Geo

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem isDerivAt0_comp_lin {g g' : ℕ} {X : Scheme.{0}} {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)}
    (he : IsHolTo Set.univ e) (L : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) {w : Fin g' → ℂ}
    {v : Sp (DualNumber ℂ) ⟶ X} (h : IsDerivAt0 (fun z => e (L z)) w v) : IsDerivAt0 e (L w) v := by
  have h0 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 := by simpa only [map_zero] using h.1
  refine ⟨h0, fun U hU f => (h.2 U hU f).trans ?_⟩
  have hmem : (0 : Fin g → ℂ) ∈ {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ e b ⁻¹ᵁ U} := by
    refine ⟨trivial, ?_⟩
    rw [← h0]
    intro x _
    exact hU (Set.mem_univ _)
  have hd : DifferentiableAt ℂ (fun z => valAt' (e z) U f) 0 :=
    ((he U f).2 0 hmem).differentiableAt ((he U f).1.mem_nhds hmem)
  let L' := LinearMap.toContinuousLinearMap L
  have hd' : HasFDerivAt (fun z => valAt' (e z) U f) (fderiv ℂ (fun z => valAt' (e z) U f) 0) (L' 0) := by
    rw [map_zero]; exact hd.hasFDerivAt
  exact DFunLike.congr_fun (hd'.comp (0 : Fin g' → ℂ) L'.hasFDerivAt).fderiv w

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {s : KA l →+* ℂ} {g g' : ℕ} {ty : Fin g → (E →+* ℂ)} {ty' : Fin g' → (E →+* ℂ)}

theorem ex_eq (F : FamilyUnif Xo s ty') (i : Fin F.n) (P : (F.Di i).La →+ (Fin g' → ℂ)) (hP : IsPeriod (F.Di i) ty' P)
    (ex : (Fin g → ℂ) → (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) (hadd : ∀ z w, ex (z + w) = ex z * ex w)
    (hol : IsHolTo Set.univ (fun z => (ex z).left)) (R : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ))
    (v : ∀ j : Fin g, epsPt (F.u i P) ⟶ Xo.univ.t.G)
    (h1 : ∀ j, IsDerivAt0 (fun z => (ex z).left) (Pi.single j 1) (v j).left)
    (h2 : ∀ j, IsDerivAt0 (fun z => (F.ex i P z).left) (R (Pi.single j 1)) (v j).left) (z : Fin g → ℂ) :
    F.ex i P (R z) = ex z := by
  have dk : DiscreteTopology {z // F.ex i P z = 1} := by
    have h0 : (fun z => F.ex i P z = 1) = fun z => z ∈ P.range := funext fun z => propext (F.ex_ker i P hP z)
    show DiscreteTopology (Subtype fun z => F.ex i P z = 1)
    rw [h0]
    exact hP.2.2.1
  have hol' := GlobalTheory.ExpChain.isHolTo_ex F i P hP
  obtain ⟨f, hf, -⟩ := existsUnique_linear_lift_fibre Xo.X Xo.X Xo.univ.t.G Xo.univ.t.G _ _ g g' ex (F.ex i P) (𝟙 _)
    (MonoidHom.id _) Xo.univ.t.semi.smooth hadd (F.ex_add i P hP) hol hol' (F.ex_diff i P hP) dk (Category.id_comp _)
    (fun x => Category.comp_id _)
  have hf : ∀ z, F.ex i P (f z) = ex z := hf
  have hfR : f = R := by
    refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
    show f (Pi.single j 1) = R (Pi.single j 1)
    have h3 : IsDerivAt0 (fun z => (F.ex i P z).left) (f (Pi.single j 1)) (v j).left :=
      isDerivAt0_comp_lin hol' f (by simpa only [hf] using h1 j)
    exact ((F.ex_diff i P hP).2 (v j) (h2 j).1).unique h3 (h2 j)
  rw [← hfR, hf]

theorem exists_transport (F : FamilyUnif Xo s ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) (x0 : Sp ℂ ⟶ Xo.X) (h : x0 = F.u i P) :
    ∃ ex : (Fin g → ℂ) → (Over.mk x0 ⟶ Xo.univ.t.G),
      (∀ z, (ex z).left = (F.ex i P z).left) ∧ (∀ z w, ex (z + w) = ex z * ex w) ∧
      (∀ w, ∃ v : epsPt x0 ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (F.ex i P z).left) w v.left) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
        toUnit _ ≫ Xo.univ.eta a = ex ((l.M : ℂ)⁻¹ • P (F.t i a)) := by
  subst h
  exact ⟨F.ex i P, fun _ => rfl, F.ex_add i P hP, fun w => ((F.ex_diff i P hP).1 w).exists, F.ex_eta i P hP⟩

theorem mark_congr {J : Type} (e : Fin g ≃ J) (e' : Fin g' ≃ J) (F : FamilyUnif Xo s ty) (F' : FamilyUnif Xo s ty')
    (i : Fin F.n) (i' : Fin F'.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (P' : (F'.Di i').La →+ (Fin g' → ℂ))
    (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F'.Di i') ty' P') (x : Sp ℂ ⟶ Xo.X) (hx : x = F.u i P)
    (hx' : x = F'.u i' P') (u : J → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left))
    (hu : ∀ j, u j ≫ Xo.univ.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x)
    (h1 : ∀ j, IsDerivAt0 (fun z => (F.ex i P z).left) (Pi.single (e.symm j) 1) (u j))
    (h2 : ∀ j, IsDerivAt0 (fun z => (F'.ex i' P' z).left) (Pi.single (e'.symm j) 1) (u j))
    (gam : (F.Di i).La → (F'.Di i').La) (hg : ∀ a j, P' (gam a) j = P a (e.symm (e' j))) :
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
      ∃ b, gam (F.t i a) = F'.t i' a + l.M • b := by
  classical
  intro a ha
  subst hx'
  obtain ⟨ex, hl, hadd, -, heta⟩ := exists_transport F i P hP _ hx
  have hl' : (fun z => (ex z).left) = fun z => (F.ex i P z).left := funext hl
  let R : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ) := LinearMap.funLeft ℂ ℂ fun j => e.symm (e' j)
  have hR : ∀ j, R (Pi.single j 1) = Pi.single (e'.symm (e j)) 1 := fun j => by
    funext k
    show (Pi.single j (1 : ℂ) : Fin g → ℂ) (e.symm (e' k)) = _
    simp only [Pi.single_apply, Equiv.symm_apply_eq, Equiv.eq_symm_apply]
  have key := ex_eq F' i' P' hP' ex hadd (by rw [hl']; exact GlobalTheory.ExpChain.isHolTo_ex F i P hP) R
    (fun j => Over.homMk (u (e j)) (hu _))
    (fun j => by rw [hl']; have := h1 (e j); rw [Equiv.symm_apply_apply] at this; exact this)
    (fun j => by rw [hR]; exact h2 (e j))
  have h3 : F'.ex i' P' ((l.M : ℂ)⁻¹ • P' (gam (F.t i a))) = F'.ex i' P' ((l.M : ℂ)⁻¹ • P' (F'.t i' a)) := by
    rw [← F'.ex_eta i' P' hP' a ha, heta a ha, ← key, map_smul]
    congr 2
    exact funext (hg _)
  have h4 : F'.ex i' P' ((l.M : ℂ)⁻¹ • P' (gam (F.t i a)) - (l.M : ℂ)⁻¹ • P' (F'.t i' a)) = 1 := by
    have h5 := F'.ex_add i' P' hP' ((l.M : ℂ)⁻¹ • P' (gam (F.t i a)) - (l.M : ℂ)⁻¹ • P' (F'.t i' a))
      ((l.M : ℂ)⁻¹ • P' (F'.t i' a))
    rw [sub_add_cancel, h3] at h5
    exact (mul_eq_right.1 h5.symm)
  obtain ⟨b, hb⟩ := (F'.ex_ker i' P' hP' _).1 h4
  have hM : (l.M : ℂ) ≠ 0 := by have := l.three_le; exact Nat.cast_ne_zero.2 (by omega)
  refine ⟨b, hP'.2.1 ?_⟩
  rw [map_add, map_nsmul, hb, ← smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hM, add_sub_cancel]

end Geo

end GlobalTheory.AdTh.MarkUniq

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.MarkUniq

theorem realM_mt {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) (h : GA D W) (τ : D.host.E →+* ℂ)
    (hτ : ∃ ρ, τ = tauE D ρ) (t : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (ht : IsInfEmb τ t) :
    realM θ (Formalism.L2.Theta.mt W h) τ = archM W t h := by
  have e : θ hτ.choose = t := GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (by
    have := hθ hτ.choose
    rwa [← hτ.choose_spec] at this) ht
  rw [realM, dif_pos hτ, ← e]
  rfl

theorem finVec_congr {D : D7} (W : HSp D) (N : ℕ) (p m q : Fin W.rank → D.host.E)
    (y w : Fin W.rank → Af D.host.F ⊗[D.host.F] D.host.E) (h : p = m + N • q) (ew : finVec W p - y = N • w) :
    finVec W m - y = N • (w - finVec W q) := by
  funext i
  have e1 := congrFun ew i
  have e2 : finVec W p i = finVec W m i + N • finVec W q i := by
    rw [h]
    exact (map_add (TensorProduct.mk D.host.F (Af D.host.F) D.host.E 1) _ _).trans
      (congrArg _ (map_nsmul (TensorProduct.mk D.host.F (Af D.host.F) D.host.E 1) _ _))
  simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul] at e1 e2 ⊢
  rw [mul_sub, ← e1, e2]
  ring

theorem rat_eq_of_archM {D : D7} (W : HSp D) {γ γ' : GA D W} (hγ : γ ∈ GQ W) (hγ' : γ' ∈ GQ W) (τ : D.host.E →+* ℂ)
    (t : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (ht : IsInfEmb τ t) (h : archM W t γ = archM W t γ') : γ = γ' := by
  have key : ∀ δ : GA D W, ∀ δ₀ : GL (Fin W.rank) D.host.E,
      (∀ i j, (matHom W δ).1 i j = (1 : AF D.host.F) ⊗ₜ δ₀.1 i j) → ∀ i j, archM W t δ i j = τ (δ₀.1 i j) := by
    intro δ δ₀ he i j
    change t (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom W δ).1 i j)) = _
    rw [he, Algebra.TensorProduct.map_tmul, map_one]
    exact ht.1 _
  obtain ⟨δ₀, -, he⟩ := hγ
  obtain ⟨δ₁, -, he'⟩ := hγ'
  have h0 : ∀ i j, (matHom W γ).1 i j = (1 : AF D.host.F) ⊗ₜ δ₀.1 i j := fun i j =>
    (congrArg (fun x : GL (Fin W.rank) (AF D.host.F ⊗[D.host.F] D.host.E) => x.1 i j) he).symm
  have h1 : ∀ i j, (matHom W γ').1 i j = (1 : AF D.host.F) ⊗ₜ δ₁.1 i j := fun i j =>
    (congrArg (fun x : GL (Fin W.rank) (AF D.host.F ⊗[D.host.F] D.host.E) => x.1 i j) he').symm
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  refine (h0 i j).trans (Eq.trans ?_ (h1 i j).symm)
  rw [τ.injective ((key γ δ₀ h0 i j).symm.trans ((congrFun (congrFun h i) j).trans (key γ' δ₁ h1 i j)))]

end GlobalTheory.AdTh.MarkUniq

open GlobalTheory.AdTh.MarkUniq in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.AdTh.dict_atComp_markAd : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → l.A = 1 → ∀ (θ : InfFam D) (W : HSp D) (hr : W.rank = r) (dict : GA D W → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ), IsInfFam θ → (∀ k, IsMod W hr (U.X k)) → (∀ k, IsOrthogonalFrame (U.X k) x₀) → (∀ k τ, IsInfEmb τ.1 (th k τ)) → DictLat U W hr dict ι e F ik φ th x₀ → ∀ (Wt : UW (Formalism.L2.PjFree.Unf.ofPj U)) (h : GA D W), IsONFr (U.X (dict h).1) (dict h).2 ∧ ∃ γ, AtComp θ W hr U.X dict x₀ h γ ∧ MarkAd l W hr ι (γ * h) (Wt.mark (dict h).1) ∧ ∀ γ', AtComp θ W hr U.X dict x₀ h γ' → γ' = γ := by
  intro D H Dw l Xo c σ r U hσ hU hr1 hA θ W hr dict ι g e F ik φ th x₀ hθ hMod hx₀ hth hD Wt h
  subst hr
  obtain ⟨γ, hγ, hΛ, hm, hfr⟩ := hD.2 h
  obtain ⟨θ', hθ'⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  obtain ⟨hAr, -, -⟩ := GlobalTheory.T.archimedeanMatrix_unitary_continuous_multiplicative D W θ' hθ'
  generalize hk : dict h = kx at hΛ hm hfr
  obtain ⟨k, x⟩ := kx
  dsimp only at hΛ hm hfr ⊢
  have hG : (U.X k).Gm = -W.gramᵀ := (hMod k).model.1
  obtain ⟨-, hu2, hu3⟩ := GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular D.host.E W.rank (U.X k).p0
    (U.X k).Ψ (U.X k).Gm (U.X k).Gm_herm
  have hfr' : ∀ τ : (U.X k).Ψ, mat x τ = archM W (θ' τ.1) (γ * h) * x₀ τ.1 := fun τ => by
    rw [hfr τ, GlobalTheory.LettersCheck.isInfEmb_unique τ.1 _ _ (hth k τ) (hθ' τ.1)]
    rfl
  have hmove : ∀ (γ' : GA D W) (τ : (U.X k).Ψ),
      mat (frMove θ W rfl (U.X k) γ' (fun τ => x₀ τ.1)) τ = archM W (θ' τ.1) γ' * x₀ τ.1 := fun γ' τ => by
    rw [← realM_mt hθ W γ' τ.1 (((hMod k).psi τ.1).1 τ.2) _ (hθ' τ.1)]
    rfl
  have hON : IsONFr (U.X k) x := fun τ => by
    rw [hfr', hu3 τ.1 _ _ (by rw [hG]; exact (hAr τ.1).2.2.2.2 _)]
    exact hx₀ k τ.1 τ.2
  have hdom : x ∈ (U.X k).dom := (hu2 x hON).1
  have hmem : ∀ v, v ∈ (U.X k).Λ ↔ v ∈ latG W (γ * h) := fun v => by
    rw [← SetLike.mem_coe, hΛ]
    exact Set.ext_iff.1 (Set.image_id _) v
  refine ⟨hON, γ, ?_, ?_, ?_⟩
  · unfold AtComp
    rw [hk]
    refine ⟨hγ, SetLike.coe_injective hΛ.symm, funext fun τ => ?_⟩
    exact (hfr' τ).trans (hmove _ τ).symm
  · intro a ha
    obtain ⟨P, hPe, hP, hy, hd⟩ := hD.1.2 k ⟨x, hdom⟩
    obtain ⟨P', hPe', hP', hy', hd', -⟩ := Wt.pt k ⟨x, hdom⟩
    have hφ : ∀ v, Wt.φ k ((Wt.φ k).symm v) = v := (Wt.φ k).apply_symm_apply
    obtain ⟨b, hb⟩ := mark_congr e Wt.e F Wt.F (ik k) (Wt.ik k) P P' hP hP' _ hy hy'
      (fun j => (U.un k ⟨x, hdom⟩).u j.1 j.2) (fun j => ((U.un k ⟨x, hdom⟩).tan j.1 j.2).1)
      (fun j => hd j.1 j.2) (fun j => hd' j.1 j.2) (fun a => (Wt.φ k).symm (φ k a)) (fun a j => by
        rw [hPe, hPe', Equiv.apply_symm_apply]
        exact congrArg (fun v : (U.X k).Λ => perFr (U.X k) x (v : Fin W.rank → D.host.E) _ _) (hφ (φ k a))) a ha
    obtain ⟨w, hw, ew⟩ := hm a ha
    have hb' : (φ k (F.t (ik k) a) : Fin W.rank → D.host.E) =
        Wt.mark k a + l.M • (Wt.φ k b : Fin W.rank → D.host.E) := by
      have := congrArg (fun z => (Wt.φ k z : Fin W.rank → D.host.E)) hb
      simp only [map_add, map_nsmul] at this
      exact (congrArg Subtype.val (hφ _)).symm.trans this
    refine ⟨w - finVec W (Wt.φ k b : Fin W.rank → D.host.E), sub_mem hw
      (((GlobalTheory.MarkCoset.latG_spec D W _).1 _).1 ((hmem _).1 (Wt.φ k b).2)), ?_⟩
    exact finVec_congr W l.M _ _ _ _ _ hb' ew
  · intro γ' hγ'
    unfold AtComp at hγ'
    rw [hk] at hγ'
    obtain ⟨hq, -, hx⟩ := hγ'
    obtain ⟨τ₀⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ (U.X k).Ψ := by
      by_cases h : ComplexEmbedding.conjugate τ₀ ∈ (U.X k).Ψ
      · exact ⟨_, h⟩
      · exact ⟨τ₀, ((U.X k).cmType τ₀).2 h⟩
    have h1 : archM W (θ' τ) (γ' * h) * x₀ τ = archM W (θ' τ) (γ * h) * x₀ τ := by
      rw [← hmove _ ⟨τ, hτ⟩, ← hfr' ⟨τ, hτ⟩]
      exact congrArg (fun y => mat y ⟨τ, hτ⟩) hx.symm
    have hdet : IsUnit (x₀ τ).det :=
      (((hu2 (fun τ => x₀ τ.1) fun τ => hx₀ k τ.1 τ.2).1 ⟨τ, hτ⟩).1).isUnit
    have h2 : archM W (θ' τ) (γ' * h) = archM W (θ' τ) (γ * h) := by
      have := congrArg (· * (x₀ τ)⁻¹) h1
      simpa only [Matrix.mul_nonsing_inv_cancel_right _ _ hdet] using this
    refine rat_eq_of_archM W hq hγ τ _ (hθ' τ) ?_
    have h3 : ∀ δ : GA D W, archM W (θ' τ) δ = archM W (θ' τ) (δ * h) * archM W (θ' τ) h⁻¹ := fun δ => by
      rw [← (hAr τ).2.1, mul_inv_cancel_right]
    rw [h3 γ', h3 γ, h2]
