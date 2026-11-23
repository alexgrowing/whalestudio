import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.ParabolicInductionCongr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicProductEquivProductOfPartition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivContraLocComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistDiscreteCsd

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.ProdReorder

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.RS.JB

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def twCongr' {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) (χ : G →* ℂˣ) :
    (twRep ρ χ).Equiv (twist σ χ) :=
  .mk φ.toLinearEquiv fun g => LinearMap.ext fun v => by
    show φ (((χ g : ℂˣ) : ℂ) • ρ g v) = ((χ g : ℂˣ) : ℂ) • σ g (φ v)
    rw [map_smul]
    congr 1
    exact LinearMap.congr_fun (φ.isIntertwining' g) v

unseal Iso i2 in
theorem fin_step {r t N : ℕ} (h : r + t = N) {V₀ V₁ V₂ : Type} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] (ρ₀ : Representation ℂ (GL (Fin N) k) V₀) (ρ₁ : Representation ℂ (GL (Fin r) k) V₁)
    (ρ₂ : Representation ℂ (GL (Fin t) k) V₂) (A₀ : RB k N) (A : RB k r) (B : RB k t) (e₀ : Nonempty (ρ₀.Equiv A₀.ρ))
    (e₁ : Nonempty (ρ₁.Equiv A.ρ)) (e₂ : Nonempty (ρ₂.Equiv B.ρ)) (hI : Iso A₀ (i2 h A B)) :
    Nonempty (ρ₀.Equiv (ind₂ (stdSum h) (extTensor ρ₁ ρ₂))) := by
  have a : Nonempty (A₀.ρ.Equiv (ind₂ (stdSum h) (extTensor A.ρ B.ρ))) := hI
  exact e₀.elim fun x => a.elim fun y => (ind₂_congr h e₁ e₂).elim fun z => ⟨(x.trans y).trans z.symm⟩

unseal mp in
theorem to_mp {c N : ℕ} (z : Fin c → IrrGL k) (h : ∑ a, (z a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin N) k) V) (e : Nonempty (ρ.Equiv (prodIrr z h))) :
    Nonempty (ρ.Equiv (mp z (stdBlocks (fun a => (z a).1) h)).ρ) := e

end Loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem locComp_unique' {a : ℕ} {V : Submodule ℂ (Sm E a)} (hV : IsDiscrete V)
    {w : HeightOneSpectrum (𝓞 E)} {σ σ' : SmIrr (GL (Fin a) (w.adicCompletion E))} (h : IsLocCompGL V w σ)
    (h' : IsLocCompGL V w σ') : Nonempty (σ.ρ.Equiv σ'.ρ) := by
  have hst : ∀ g, ∀ φ ∈ V, finRep E a (locGL E a w g) φ ∈ V := fun g φ hφ => hV.stable (.fin _) φ hφ
  let ρV : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V :=
    { toFun := fun g => (finRep E a (locGL E a w g)).restrict (hst g)
      map_one' := LinearMap.ext fun φ => Subtype.ext (by simp)
      map_mul' := fun g g' => LinearMap.ext fun φ => Subtype.ext (by simp) }
  have := σ.irred
  have := σ'.irred
  obtain ⟨f', h0', h1', h2'⟩ := h'
  refine LocUniq.equiv_of_isoPart σ.ρ σ'.ρ ρV ?_ ⟨f'.codRestrict V h1', fun g => LinearMap.ext fun v =>
    Subtype.ext (h2' g v)⟩ fun e => h0' (LinearMap.ext fun v => by
      have := congrArg (fun F : σ'.ρ.IntertwiningMap ρV => (F.toLinearMap v : Sm E a)) e
      simpa using this)
  refine eq_top_iff.2 fun x _ => ?_
  have hx : x.1 ∈ ⨆ f : GlobalTheory.LocDual.Maps V w σ, LinearMap.range f.1 := by
    rw [GlobalTheory.LocDual.iSup_range_eq V hV.stable hV.irred w σ h]; exact x.2
  have hle : (⨆ f : GlobalTheory.LocDual.Maps V w σ, LinearMap.range f.1) ≤
      (LocUniq.isoPart σ.ρ ρV).map V.subtype := by
    refine iSup_le fun f => ?_
    rintro _ ⟨v, rfl⟩
    exact ⟨⟨f.1 v, f.2.1 v⟩, Submodule.mem_iSup_of_mem (⟨f.1.codRestrict V f.2.1, fun g => LinearMap.ext fun u =>
      Subtype.ext (f.2.2 g u)⟩ : σ.ρ.IntertwiningMap ρV) ⟨v, rfl⟩, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hle hx
  obtain rfl : y = x := Subtype.ext hyx
  exact hy

theorem of_eq_of_locComp' {w : HeightOneSpectrum (𝓞 E)} {x y : Σ M : ℕ, Submodule ℂ (Sm E M)}
    (hxy : x = y) (hV : IsDiscrete x.2) (σ : SmIrr (GL (Fin x.1) (w.adicCompletion E)))
    (σ' : SmIrr (GL (Fin y.1) (w.adicCompletion E))) (h : IsLocCompGL x.2 w σ) (h' : IsLocCompGL y.2 w σ') :
    IrrGL.of σ.ρ σ.smooth σ.irred = IrrGL.of σ'.ρ σ'.smooth σ'.irred := by
  subst hxy
  exact IrrGL.of_eq_of.2 (locComp_unique' hV h h')

def twLoc {w : HeightOneSpectrum (𝓞 E)} {M : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin M) (w.adicCompletion E)) V) (χ : HChar E) :
    (twRep ρ (CuspSub.locDet M χ w)).Equiv (twist ρ (GlobalTheory.SmGL.detChar (Fin M) (χ.loc w))) :=
  .mk (LinearEquiv.refl ℂ V) fun _ => LinearMap.ext fun _ => rfl

def twCls {m : ℕ} (χ : HChar E) (P : Pre E m) (w : HeightOneSpectrum (𝓞 E)) :
    Fin P.c → IrrGL (w.adicCompletion E) :=
  fun j => (P.cls j w).tw (χ.loc w) (ParLaws.isSmoothChar_loc χ w)

theorem cls_tw {n M : ℕ} (D : Pre E n) (i : Fin D.c) (χ : HChar E) {w : HeightOneSpectrum (𝓞 E)}
    (V : Submodule ℂ (Sm E M)) (σ : SmIrr (GL (Fin M) (w.adicCompletion E))) (hσ : IsLocCompGL V w σ)
    (hi : (⟨D.N i, D.V i⟩ : Σ M : ℕ, Submodule ℂ (Sm E M)) = twPart χ ⟨M, V⟩) :
    D.cls i w = (IrrGL.of σ.ρ σ.smooth σ.irred).tw (χ.loc w) (ParLaws.isSmoothChar_loc χ w) := by
  rw [IrrGL.tw_of]
  have h1 := of_eq_of_locComp' hi (D.discrete i) (D.σ i w)
    (σ.twist (CuspSub.locDet M χ w) (CuspSub.isOpen_ker_locDet χ w)) (D.loc i w)
    (TwistDisc.isLocCompGL_map χ hσ)
  exact h1.trans (IrrGL.of_eq_of.2 ⟨twLoc σ.ρ χ⟩)

theorem join_parts {n a b : ℕ} {χ₁ χ₂ : HChar E} {Pa : Pre E a} {Pb : Pre E b} {D : Pre E n}
    (hJ : IsJoin χ₁ χ₂ Pa Pb D) : ∃ hc : D.c = Pa.c + Pb.c, ∀ i : Fin (Pa.c + Pb.c),
      (⟨D.N (Fin.cast hc.symm i), D.V (Fin.cast hc.symm i)⟩ : Σ M : ℕ, Submodule ℂ (Sm E M)) =
        Fin.append (fun j => twPart χ₁ ⟨Pa.N j, Pa.V j⟩) (fun j => twPart χ₂ ⟨Pb.N j, Pb.V j⟩) i := by
  have e : List.ofFn (fun i => (⟨D.N i, D.V i⟩ : Σ M : ℕ, Submodule ℂ (Sm E M))) =
      List.ofFn (Fin.append (fun j => twPart χ₁ ⟨Pa.N j, Pa.V j⟩) (fun j => twPart χ₂ ⟨Pb.N j, Pb.V j⟩)) := by
    have hJ' : parts D = (parts Pa).map (twPart χ₁) ++ (parts Pb).map (twPart χ₂) := hJ
    unfold parts at hJ'
    rw [hJ', List.map_ofFn, List.map_ofFn, List.ofFn_fin_append]
    rfl
  obtain ⟨hc, hf⟩ := Sigma.mk.inj_iff.1 (List.ofFn_inj'.1 e)
  exact ⟨hc, fun i => (Fin.heq_fun_iff hc).1 hf (Fin.cast hc.symm i)⟩

theorem cls_append {n a b : ℕ} {χ₁ χ₂ : HChar E} {Pa : Pre E a} {Pb : Pre E b} {D : Pre E n} (w : HeightOneSpectrum (𝓞 E))
    (hc : D.c = Pa.c + Pb.c) (hD : ∀ i : Fin (Pa.c + Pb.c),
      (⟨D.N (Fin.cast hc.symm i), D.V (Fin.cast hc.symm i)⟩ : Σ M : ℕ, Submodule ℂ (Sm E M)) =
        Fin.append (fun j => twPart χ₁ ⟨Pa.N j, Pa.V j⟩) (fun j => twPart χ₂ ⟨Pb.N j, Pb.V j⟩) i) :
    ∀ i, Fin.append (twCls χ₁ Pa w) (twCls χ₂ Pb w) i = D.cls (Fin.cast hc.symm i) w := by
  intro i
  refine Fin.addCases (motive := fun i =>
    Fin.append (twCls χ₁ Pa w) (twCls χ₂ Pb w) i = D.cls (Fin.cast hc.symm i) w) (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]
    have hi := hD (Fin.castAdd Pb.c j)
    rw [Fin.append_left] at hi
    exact (cls_tw D _ χ₁ (Pa.V j) (Pa.σ j w) (Pa.loc j w) hi).symm
  · rw [Fin.append_right]
    have hi := hD (Fin.natAdd Pa.c j)
    rw [Fin.append_right] at hi
    exact (cls_tw D _ χ₂ (Pb.V j) (Pb.σ j w) (Pb.loc j w) hi).symm

theorem twist_lp {a : ℕ} (χ : HChar E) (P : Pre E a) (w : HeightOneSpectrum (𝓞 E)) :
    Nonempty ((twRep (lp P w) ((χ.loc w).comp GeneralLinearGroup.det)).Equiv (prodIrr (twCls χ P w) P.h)) :=
  ⟨(twCongr' (prodIrrEquiv P.h (fun j => (P.σ j w).ρ) (fun j => (P.σ j w).smooth)
    fun j => (P.σ j w).irred) _).trans
    (prodIrrTwistEquiv (fun j => P.cls j w) P.h (χ.loc w) (ParLaws.isSmoothChar_loc χ w))⟩

theorem lp_equiv {n : ℕ} (D : Pre E n) (w : HeightOneSpectrum (𝓞 E)) :
    Nonempty ((lp D w).Equiv (prodIrr (fun i => D.cls i w) D.h)) :=
  ⟨prodIrrEquiv D.h (fun i => (D.σ i w).ρ) (fun i => (D.σ i w).smooth) fun i => (D.σ i w).irred⟩

theorem cls_list {n a b : ℕ} {χ₁ χ₂ : HChar E} {Pa : Pre E a} {Pb : Pre E b} {D : Pre E n} (w : HeightOneSpectrum (𝓞 E))
    (hJ : IsJoin χ₁ χ₂ Pa Pb D) :
    List.ofFn (fun i => D.cls i w) = List.ofFn (twCls χ₁ Pa w) ++ List.ofFn (twCls χ₂ Pb w) := by
  obtain ⟨hc, hD⟩ := join_parts hJ
  rw [← List.ofFn_fin_append, List.ofFn_congr hc]
  exact congrArg List.ofFn (funext fun i => (cls_append w hc hD i).symm)

theorem joinMod_holds : JoinMod := fun _ _ _ _ _ _ _ h χ₁ χ₂ Pa Pb D w hJ =>
  fin_step h _ _ _ _ _ _ (to_mp (fun i => D.cls i w) D.h _ (lp_equiv D w))
    (to_mp (twCls χ₁ Pa w) Pa.h _ (twist_lp χ₁ Pa w)) (to_mp (twCls χ₂ Pb w) Pb.h _ (twist_lp χ₂ Pb w))
    (stagesB _ _ _ _ _ _ (cls_list w hJ) h _ _ _)

end PositivityTheory.Rg.BcB.F.RS.JB

end
