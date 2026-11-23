import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.FinKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.AdSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.UaFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.MemDxIff

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.Dict.Br

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

private theorem ad_ext {a b : Ad L} (hi : pInf L a = pInf L b)
    (hf : ∀ w : Plc L, pLoc L w (pFin L a) = pLoc L w (pFin L b)) : a = b := by
  apply Prod.ext
  · exact (infEq L).symm.injective hi
  · apply Subtype.ext
    funext w
    exact hf w

private theorem det_mL (x : UA L 2) (w : Plc L) :
    (mL w x).det = pLoc L w (pFin L ((x : GL (Fin 2) (Ad L)) : Matrix (Fin 2) (Fin 2) (Ad L)).det) := by
  have h : mL w x = ((pLoc L w).comp (pFin L)).mapMatrix ((x : GL (Fin 2) (Ad L)) : Matrix (Fin 2) (Fin 2) (Ad L)) := rfl
  rw [h, ← RingHom.map_det]
  rfl

private theorem det_inf (x : UA L 2) (hx : x ∈ finU L 2) :
    pInf L ((x : GL (Fin 2) (Ad L)) : Matrix (Fin 2) (Fin 2) (Ad L)).det = 1 := by
  have h : (pInf L).mapMatrix ((x : GL (Fin 2) (Ad L)) : Matrix (Fin 2) (Fin 2) (Ad L)) = 1 := by
    have h1 : cInf x = 1 := hx
    exact congrArg (fun y : GL (Fin 2) (Cinf L) => (y : Matrix (Fin 2) (Fin 2) (Cinf L))) h1
  rw [RingHom.map_det, h, Matrix.det_one]

private theorem mem_SUA_iff (x : UA L 2) (hx : x ∈ finU L 2) :
    x ∈ SUA L ↔ ∀ w : Plc L, (mL w x).det = 1 := by
  have key : x ∈ SUA L ↔ ((x : GL (Fin 2) (Ad L)) : Matrix (Fin 2) (Fin 2) (Ad L)).det = 1 := by
    show GeneralLinearGroup.det (x : GL (Fin 2) (Ad L)) = 1 ↔ _
    rw [Units.ext_iff]
    rfl
  rw [key]
  constructor
  · intro h w
    rw [det_mL, h, map_one, map_one]
  · intro h
    apply ad_ext
    · rw [det_inf x hx, map_one]
    · intro w
      rw [← det_mL, h w, map_one, map_one]

private theorem mem_KD {K O : Type} [Field K] [CommRing O] [Algebra O K] {Δ : K} (g : DX Δ) (hd : (mt g).det = 1)
    (hi : ∀ i j, IsIntegral O (mt g i j)) : g ∈ KD Δ O := by
  let M : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ)) := fun i j => ⟨mt g i j, hi i j⟩
  have hM : ((integralClosure O (Lsq K Δ)).val : integralClosure O (Lsq K Δ) →+* Lsq K Δ).mapMatrix M = mt g := by
    ext i j <;> rfl
  have hdet : M.det = 1 := by
    apply Subtype.ext
    have := RingHom.map_det ((integralClosure O (Lsq K Δ)).val : integralClosure O (Lsq K Δ) →+* Lsq K Δ) M
    rw [hM, hd] at this
    exact this
  refine ⟨GeneralLinearGroup.mk'' M (by rw [hdet]; exact isUnit_one), ?_⟩
  ext i j <;> rfl

private theorem SA_det {Δ : Lp L} (g : SA Δ) (v : Pl (Lp L)) : (mt ((g : DA Δ).1 v)).det = 1 := by
  have h := (Subgroup.mem_iInf.1 g.2) v
  have h2 : GeneralLinearGroup.det (((g : DA Δ).1 v : DX (cv v Δ)) : GL (Fin 2) (Lsq (Kv v) (cv v Δ))) = 1 := h
  exact congrArg Units.val h2

private theorem ex_of (R : RingBr L) (g : SA R.Δ) : ∃ b : ↥(finU L 2 ⊓ SUA L), ∀ w,
    mL w (b : UA L 2) = (mt ((g : DA R.Δ).1 (un w))).map (R.ρ _ w rfl) := by
  have hun : ∀ v, star (mt ((g : DA R.Δ).1 v)) * mt ((g : DA R.Δ).1 v) = 1 := by
    intro v
    rw [((suIff (Kv v) (cv v R.Δ)).1 _).1, SA_det, one_smul]
  have hint : ∀ᶠ v in Filter.cofinite, ∀ i j, IsIntegral (Ov v) (mt ((g : DA R.Δ).1 v) i j) := by
    refine Filter.Eventually.mono (g : DA R.Δ).2 ?_
    intro v hv
    obtain ⟨m, hm⟩ := hv
    intro i j
    have h : mt ((g : DA R.Δ).1 v) i j = (((m : Matrix (Fin 2) (Fin 2) (integralClosure (Ov v) (Lsq (Kv v) (cv v R.Δ)))) i j : integralClosure (Ov v) (Lsq (Kv v) (cv v R.Δ))) : Lsq (Kv v) (cv v R.Δ)) := by
      exact congrArg (fun z : GL (Fin 2) (Lsq (Kv v) (cv v R.Δ)) => (z : Matrix (Fin 2) (Fin 2) (Lsq (Kv v) (cv v R.Δ))) i j) hm.symm
    rw [h]
    exact ((m : Matrix (Fin 2) (Fin 2) (integralClosure (Ov v) (Lsq (Kv v) (cv v R.Δ)))) i j).2
  obtain ⟨b, hb, hloc⟩ := adEx L R 2 (fun v => mt ((g : DA R.Δ).1 v)) hun hint
  refine ⟨⟨b, hb, ?_⟩, hloc⟩
  refine (mem_SUA_iff b hb).2 fun w => ?_
  rw [hloc w]
  have h := RingHom.map_det (R.ρ _ w rfl) (mt ((g : DA R.Δ).1 (un w)))
  rw [SA_det, map_one] at h
  exact h.symm

private theorem sep_of (x y : ↥(finU L 2 ⊓ SUA L)) (h : ∀ w, mL w (x : UA L 2) = mL w (y : UA L 2)) : x = y := by
  obtain ⟨-, -, -, -, hsep, hfin, -, -⟩ := uaFacts L 2
  exact Subtype.ext (hsep _ _ (fun w => Units.ext (h w))
    fun τ => (((hfin _).1.1 x.2.1) τ).trans (((hfin _).1.1 y.2.1) τ).symm)

end UpperTheory.V.Z.Sym.Dict.Br

theorem UpperTheory.V.Z.Sym.Dict.Br.bSEx :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (R : RingBr L), ∃ b : SA R.Δ ≃* ↥(finU L 2 ⊓ SUA L), ∀ g w, mL w (b g : UA L 2) = (mt ((g : DA R.Δ).1 (un w))).map (R.ρ _ w rfl) := by
  intro L _ _ _ R
  choose f hf using ex_of R
  have hmul : ∀ g h, f (g * h) = f g * f h := by
    intro g h
    refine sep_of _ _ fun w => ?_
    have h1 : mL w ((f g * f h : ↥(finU L 2 ⊓ SUA L)) : UA L 2) = mL w (f g : UA L 2) * mL w (f h : UA L 2) := by
      simp only [mL, Subgroup.coe_mul, map_mul, Units.val_mul]
    rw [h1, hf, hf, hf, ← Matrix.map_mul]
    rfl
  have hinj : Function.Injective f := by
    intro g h e
    have hv : ∀ v, mt ((g : DA R.Δ).1 v) = mt ((h : DA R.Δ).1 v) := by
      intro v
      refine Matrix.ext fun i j => sub_eq_zero.1 (R.ρ_inj v _ fun w hw => ?_)
      subst hw
      have h1 := (hf g w).symm.trans ((congrArg (fun b : ↥(finU L 2 ⊓ SUA L) => mL w (b : UA L 2)) e).trans (hf h w))
      have h2 := congrFun (congrFun h1 i) j
      rw [map_sub, sub_eq_zero]
      exact h2
    exact Subtype.ext (Subtype.ext (funext fun v => Subtype.ext (Units.ext (hv v))))
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hyF, hyS⟩
    obtain ⟨x, hu, hi, hl⟩ := adSurj L R 2 y
    have hdet : ∀ v, (x v).det = 1 := by
      intro v
      refine sub_eq_zero.1 (R.ρ_inj v _ fun w hw => ?_)
      subst hw
      have h1 := RingHom.map_det (R.ρ _ w rfl) (x (un w))
      have h2 : (R.ρ _ w rfl).mapMatrix (x (un w)) = mL w y := (hl w).symm
      rw [map_sub, map_one, h1, h2, (mem_SUA_iff y hyF).1 hyS w, sub_self]
    choose d hd using fun v => (suIff (Kv v) (cv v R.Δ)).2 (x v) (hu v) (hdet v)
    have hmem : ∀ᶠ v in Filter.cofinite, d v ∈ KD (cv v R.Δ) (Ov v) :=
      hi.mono fun v hv => mem_KD (d v) (by rw [hd]; exact hdet v) (by rw [hd]; exact hv)
    let g0 : DA R.Δ := ⟨d, hmem⟩
    have hg0 : g0 ∈ SA R.Δ := by
      refine Subgroup.mem_iInf.2 fun v => ?_
      show GeneralLinearGroup.det ((d v : DX (cv v R.Δ)) : GL (Fin 2) (Lsq (Kv v) (cv v R.Δ))) = 1
      refine Units.ext ?_
      show (mt (d v)).det = 1
      rw [hd]
      exact hdet v
    refine ⟨⟨g0, hg0⟩, sep_of _ _ fun w => ?_⟩
    rw [hf]
    show (mt (d (un w))).map (R.ρ _ w rfl) = mL w y
    rw [hd, hl]
  exact ⟨MulEquiv.ofBijective (MonoidHom.mk' f hmul) ⟨hinj, hsurj⟩, fun g w => hf g w⟩
