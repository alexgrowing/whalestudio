import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainSharpColumnValuationOfPointKernelLiftL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianLatticeChartFamilyLawBasis

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

noncomputable section

namespace GlobalTheory.LvT.Built.KerExt

theorem exists_ext {G P T β X : Type} [Group G] [MulAction G P] [Group T] {H D : β → Type} [∀ b, Group (H b)]
    [∀ b, MulAction (H b) (D b)] (ρ : G → X → X) (ρ1 : ∀ x, ρ 1 x = x) (ρm : ∀ g h x, ρ (g * h) x = ρ g (ρ h x))
    (pt : ∀ b, D b → P) (hom : ∀ b, H b →* G) (zeta : T →* G)
    (pt_smul : ∀ b g d, pt b (g • d) = hom b g • pt b d)
    (gen : ∀ b (g : G), ∃ ζ g', g = zeta ζ * hom b g')
    (comm : ∀ ζ (g : G), zeta ζ * g = g * zeta ζ)
    (surj : ∀ p : P, ∃ ζ b d, p = zeta ζ • pt b d)
    (idx : ∀ ζ b b' d d', zeta ζ • pt b d = pt b' d' → b = b')
    (inj : ∀ ζ b d d', zeta ζ • pt b d = pt b d' → ∃ g : H b, g • d = d' ∧ ∀ x, ρ (hom b g) x = ρ (zeta ζ) x)
    (φ : ∀ b, D b → X) (hφ : ∀ b g d, φ b (g • d) = ρ (hom b g) (φ b d)) :
    ∃ Φ : P → X, (∀ b d, Φ (pt b d) = φ b d) ∧ ∀ g p, Φ (g • p) = ρ g (Φ p) := by
  have key : ∀ g ζ b d ζ' b' d', g • zeta ζ • pt b d = zeta ζ' • pt b' d' →
      ρ (zeta ζ') (φ b' d') = ρ g (ρ (zeta ζ) (φ b d)) := by
    intro g ζ b d ζ' b' d' h
    obtain ⟨ζ₀, g₀, rfl⟩ := gen b g
    have e : zeta (ζ'⁻¹ * ζ₀ * ζ) * hom b g₀ = (zeta ζ')⁻¹ * (zeta ζ₀ * hom b g₀ * zeta ζ) := by
      rw [map_mul, map_mul, map_inv, mul_assoc, comm ζ]
      simp only [mul_assoc]
    have h1 : zeta (ζ'⁻¹ * ζ₀ * ζ) • pt b (g₀ • d) = pt b' d' := by
      rw [pt_smul, ← mul_smul, e, mul_smul, mul_smul, h, inv_smul_smul]
    obtain rfl := idx _ _ _ _ _ h1
    obtain ⟨g₁, rfl, hg⟩ := inj _ _ _ _ h1
    rw [hφ, hg, hφ, ← ρm, ← ρm, ← ρm, mul_assoc, e, mul_inv_cancel_left]
  choose z i d hp using surj
  refine ⟨fun p => ρ (zeta (z p)) (φ (i p) (d p)), fun b x => ?_, fun g p => ?_⟩
  · have := key 1 1 b x (z (pt b x)) (i (pt b x)) (d (pt b x)) (by rw [← hp, map_one, one_smul, one_smul])
    exact this.trans (by rw [map_one, ρ1, ρ1])
  · exact key g (z p) (i p) (d p) _ _ _ (by rw [← hp, ← hp])

theorem exists_cplx {K V V' W W' : Type} [Field K] (σ : K →+* ℂ) [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (e : V →ₛₗ[σ] W) (e' : V' →ₛₗ[σ] W')
    (li : LinearIndependent ℂ fun j => e (Module.Basis.ofVectorSpace K V j))
    (sp : Submodule.span ℂ (Set.range e) = ⊤) (f : V →ₗ[K] V') :
    ∃ fC : W →ₗ[ℂ] W', ∀ F, fC (e F) = e' (f F) := by
  set b := Module.Basis.ofVectorSpace K V
  have hmem : ∀ F, e F ∈ Submodule.span ℂ (Set.range fun j => e (b j)) := by
    intro F
    have hF : F ∈ Submodule.span K (Set.range b) := by rw [b.span_eq]; trivial
    induction hF using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact Submodule.subset_span ⟨j, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  have sp' : ⊤ ≤ Submodule.span ℂ (Set.range fun j => e (b j)) := by
    rw [← sp, Submodule.span_le]
    rintro _ ⟨F, rfl⟩
    exact hmem F
  let c := Module.Basis.mk li sp'
  refine ⟨c.constr ℂ fun j => e' (f (b j)), fun F => ?_⟩
  have h : (c.constr ℂ fun j => e' (f (b j))).comp e = e'.comp f := by
    refine b.ext fun j => ?_
    have : e (b j) = c j := by simp [c]
    simp only [LinearMap.comp_apply, this, Module.Basis.constr_basis]
  exact LinearMap.congr_fun h F

section Real

variable {D : D7} {u : D.what₂.Word} {B : Built.Dat D u} {i : ℕ} {sp : Split (B.J.A i) B.J.T} {M : PtModel B.ch i}
  (R : B.Real i sp M)

def evM : B.V i →ₛₗ[D.what₂.embLL] M.Val :=
  LinearMap.codRestrict M.Val (evV B.emb (1 : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) B.E) (B.lam i) D.what₂.embLL)
    fun F => by rw [R.val_eq]; exact evV_mem_ValC _ _ _ _ F

theorem evM_li : LinearIndependent ℂ fun j => evM R (Module.Basis.ofVectorSpace D.what₂.LL (B.V i) j) :=
  LinearIndependent.of_comp M.Val.subtype
    (evV_linearIndependent B.emb 1 (B.lam i) D.what₂.embLL (fr0 B.emb D.what₂.embLL _) _
      (Module.Basis.ofVectorSpace D.what₂.LL (B.V i)).linearIndependent)

theorem evM_span : Submodule.span ℂ (Set.range (evM R)) = ⊤ := by
  apply Submodule.map_injective_of_injective M.Val.subtype_injective
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
  exact (span_evV B.emb 1 (B.lam i) D.what₂.embLL).trans R.val_eq.symm

theorem evM_rho (b) (g : (B.I.S i).G b) (F : B.V i) :
    evM R ((B.I.S i).rho B.emb (B.lam i) b g F) = M.act (R.hom b g) (evM R F) := by
  apply Subtype.ext
  rw [R.act_hom]
  exact GStep.evV_rho_eq_tr _ _ _ _ b g F

theorem inj_act (ζ b d d') (h : R.zeta ζ • R.pt b d = R.pt b d') :
    ∃ g : (B.I.S i).G b, g • d = d' ∧ M.act (R.hom b g) = M.act (R.zeta ζ) := by
  obtain ⟨g, h1, h2, h3⟩ := (R.inj ζ b d d').1 h
  refine ⟨g, h3, LinearMap.ext fun y => Subtype.ext ?_⟩
  rw [R.act_hom, R.act_zeta]
  funext x
  refine (trFr_apply B.emb D.what₂.embLL ((B.I.S i).gam b g) ((B.I.S i).chr b g) y.1 x).trans ?_
  rw [h1, h2, inv_one, frMul_one]
  rfl

theorem inj_act_inv (ζ b) (g : (B.I.S i).G b) (h : M.act (R.hom b g) = M.act (R.zeta ζ)) :
    M.act (R.hom b g)⁻¹ = M.act (R.zeta ζ)⁻¹ := by
  calc M.act (R.hom b g)⁻¹ = M.act (R.hom b g)⁻¹ * (M.act (R.zeta ζ) * M.act (R.zeta ζ)⁻¹) := by
        rw [← map_mul, mul_inv_cancel, map_one, mul_one]
    _ = _ := by rw [← h, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

theorem ext_evM {W : Type} [AddCommGroup W] [Module ℂ W] {f g : M.Val →ₗ[ℂ] W} (h : ∀ F, f (evM R F) = g (evM R F)) :
    f = g :=
  LinearMap.ext_on_range (evM_span R) h

end Real

theorem exists_kerPt : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) , Built.Dat.KerEq k → ∃ K : KerPt M M', K.TgtEq ∧ Built.Dat.KerIs R R' K k := by
  intro D u B i sp sp' M M' R R' k hk
  choose kC hkC using fun b b' d d' =>
    exists_cplx D.what₂.embLL (evM R) (evM R') (evM_li R) (evM_span R) (k b b' d d')
  have hequiv : ∀ b b' (g : (B.I.S i).G b) (g' : (B.I.S (i + 1)).G b') d d',
      kC b b' (g • d) (g' • d') = M'.act (R'.hom b' g') ∘ₗ kC b b' d d' ∘ₗ M.act (R.hom b g)⁻¹ := by
    intro b b' g g' d d'
    refine ext_evM R fun F => ?_
    rw [hkC, hk.equiv, ← map_inv]
    simp only [LinearMap.comp_apply]
    rw [evM_rho, ← evM_rho R, hkC]

  have h1 : ∀ b d, ∃ Φ : M'.Pt → (M.Val →ₗ[ℂ] M'.Val), (∀ b' d', Φ (R'.pt b' d') = kC b b' d d') ∧
      ∀ (g : M'.G) p, Φ (g • p) = M'.act g ∘ₗ Φ p := by
    intro b d
    refine exists_ext (fun (g : M'.G) (x : M.Val →ₗ[ℂ] M'.Val) => M'.act g ∘ₗ x) ?_ ?_ R'.pt R'.hom R'.zeta R'.pt_smul
      R'.gen R'.comm R'.surj (fun ζ b b' d d' h => R'.idx ζ b b' d d' (congrArg Prod.fst h)) ?_
      (fun b' d' => kC b b' d d') ?_
    · intro x
      simp only [map_one]
      rfl
    · intro g h x
      simp only [map_mul]
      rfl
    · intro ζ b' d₁ d₂ h
      obtain ⟨g, h1, h2⟩ := inj_act R' ζ b' d₁ d₂ h
      exact ⟨g, h1, fun x => by simp only [h2]⟩
    · intro b' g d'
      have := hequiv b b' 1 g d d'
      rw [one_smul, map_one, inv_one, map_one] at this
      exact this
  choose Φ hΦ hΦe using h1

  obtain ⟨Ψ, hΨ, hΨe⟩ : ∃ Ψ : M.Pt → M'.Pt → (M.Val →ₗ[ℂ] M'.Val), (∀ b d, Ψ (R.pt b d) = Φ b d) ∧
      ∀ (g : M.G) p, Ψ (g • p) = fun p' => Ψ p p' ∘ₗ M.act g⁻¹ := by
    refine exists_ext (fun (g : M.G) (x : M'.Pt → (M.Val →ₗ[ℂ] M'.Val)) p' => x p' ∘ₗ M.act g⁻¹) ?_ ?_ R.pt R.hom R.zeta
      R.pt_smul R.gen R.comm R.surj (fun ζ b b' d d' h => R.idx ζ b b' d d' (congrArg Prod.fst h)) ?_ Φ ?_
    · intro x
      simp only [inv_one, map_one]
      rfl
    · intro g h x
      simp only [mul_inv_rev, map_mul]
      rfl
    · intro ζ b d₁ d₂ h
      obtain ⟨g, h1, h2⟩ := inj_act R ζ b d₁ d₂ h
      exact ⟨g, h1, fun x => by simp only [inj_act_inv R ζ b g h2]⟩
    · intro b g d
      funext p'
      obtain ⟨ζ, b', d', rfl⟩ := R'.surj p'
      have := hequiv b b' g 1 d d'
      rw [one_smul, map_one, map_one] at this
      simp only [hΦe, hΦ, this]
      rfl
  have hpt : ∀ b b' d d', Ψ (R.pt b d) (R'.pt b' d') = kC b b' d d' := fun b b' d d' => by rw [hΨ, hΦ]
  refine ⟨⟨Ψ, fun g p p' y => ?_, fun c c' y => ?_⟩, fun g' p p' y => ?_, fun b b' d d' F y hy => ?_⟩
  · rw [hΨe]
    show Ψ p p' ((M.act g⁻¹ * M.act g) y) = _
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  · rw [R.rep_eq, R'.rep_eq, hpt]
    have : B.ch.C.Kmap i c c' ∘ₗ M.Val.subtype =
        M'.Val.subtype ∘ₗ kC c.1 c'.1 ((B.I.S i).rep c) ((B.I.S (i + 1)).rep c') := by
      refine ext_evM R fun F => ?_
      simp only [LinearMap.comp_apply]
      rw [hkC]
      exact hk.kmap c c' F
    exact LinearMap.congr_fun this y
  · obtain ⟨ζ, b, d, rfl⟩ := R.surj p
    show Ψ _ _ y = M'.act g' (Ψ _ _ y)
    simp only [hΨe, hΨ, hΦe]
    rfl
  · obtain rfl : y = evM R F := Subtype.ext hy
    show (Ψ _ _ _).1 = _
    rw [hpt, hkC]
    rfl

end GlobalTheory.LvT.Built.KerExt
