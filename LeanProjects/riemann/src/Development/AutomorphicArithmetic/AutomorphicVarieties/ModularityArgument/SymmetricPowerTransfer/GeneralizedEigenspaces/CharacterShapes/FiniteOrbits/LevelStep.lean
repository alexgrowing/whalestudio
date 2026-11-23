import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.FinToAF
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.ExpoMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.OutInvMulMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.DcAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.ExpoEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.UaFacts

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem finOrb_sub {G : Type} [Group G] (U H : Subgroup G) (x : H)
    (h : UpperTheory.V.AlgebraTools.FinOrb U U (x : G)) : UpperTheory.V.AlgebraTools.FinOrb (U.subgroupOf H) (U.subgroupOf H) x := by
  let f : H ⧸ U.subgroupOf H → G ⧸ U := fun q => Quotient.liftOn' q (fun y => ((y : G) : G ⧸ U)) (by
    intro y z hyz
    have hyz' : y⁻¹ * z ∈ U.subgroupOf H := QuotientGroup.leftRel_apply.1 hyz
    exact QuotientGroup.eq.2 (by simpa [Subgroup.mem_subgroupOf] using hyz'))
  have hf : Function.Injective f := by
    intro q q'
    induction q using QuotientGroup.induction_on with | _ y => ?_
    induction q' using QuotientGroup.induction_on with | _ z => ?_
    intro hyz
    have hyz' : (y : G)⁻¹ * z ∈ U := QuotientGroup.eq.1 hyz
    exact QuotientGroup.eq.2 (by simpa [Subgroup.mem_subgroupOf] using hyz')
  refine Set.Finite.of_finite_image (f := f) (Set.Finite.subset h ?_) hf.injOn
  rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
  exact ⟨⟨(u.1 : G), u.2⟩, rfl⟩

section
variable {L : Type} [Field L] [NumberField L] [IsCMField L]

private theorem fin_uniq (f f' : finU L 3) (k k' : UA L 3) (hk : k ∈ infU L 3) (hk' : k' ∈ infU L 3)
    (he : (f : UA L 3) * k = (f' : UA L 3) * k') : f = f' ∧ k = k' := by
  obtain ⟨-, -, -, -, hext, hfi, -, -⟩ := Br.uaFacts L 3
  have hff : (f : UA L 3) = f' := by
    refine hext _ _ (fun w => ?_) (fun τ => ?_)
    · have h1 := congrArg (cLoc w) he
      rw [map_mul, map_mul, ((hfi k).2.1 hk) w, ((hfi k').2.1 hk') w, mul_one, mul_one] at h1
      exact h1
    · rw [((hfi _).1.1 f.2) τ, ((hfi _).1.1 f'.2) τ]
  refine ⟨Subtype.ext hff, ?_⟩
  rw [hff] at he
  exact mul_left_cancel he

private theorem inf_eq (B : Bridge L) (j : ℕ) (γ : U3 B.Δ) (k : UA L 3)
    (hτ : ∀ τ, cEmb τ k = cEmb τ (B.rG γ : UA L 3)) :
    Wt.cG (em B) j γ = Wt.repG _ j (infC L 3 k) := by
  have hinf : infC L 3 k = Wt.infG (em B) 3 (Unitary.toUnits γ) := by
    funext v
    refine Units.ext ?_
    show (cEmb v.embedding k : Matrix (Fin 3) (Fin 3) ℂ) = _
    rw [hτ v.embedding, B.rG_inf]
    rfl
  rw [hinf]
  rfl

private theorem left_step (B : Bridge L) (hB : B.Ok) (A : SD B.Δ) (j : ℕ) (ch : Lp L → ℂ)
    (C : Base (U3 B.Δ) (GA B.Δ) (Wt.VG (InfinitePlace L) j)) (s : C.Tw) (hBG : A.dat.IsBG ch C s)
    (hW : C.W = Wt.cG (em B) j) (ψ : GA B.Δ → Wt.VG (InfinitePlace L) j) (hψ : ψ ∈ C.Forms)
    (f : finU L 3) (k : UA L 3) (hk : k ∈ infU L 3) (hfk : (f : UA L 3) * k ∈ ratU L 3) (g : finU L 3) :
    ψ (B.bG.symm (f * g)) = Wt.repG _ j (infC L 3 k) (ψ (B.bG.symm g)) := by
  obtain ⟨γ, hγ⟩ : ∃ γ : U3 B.Δ, (B.rG γ : UA L 3) = f * k :=
    ⟨B.rG.symm ⟨_, hfk⟩, by rw [MulEquiv.apply_symm_apply]⟩
  obtain ⟨k', hk', he, hτ⟩ := hB.finG γ (C.ι γ) (fun v => hBG.ι γ v)
  obtain ⟨g0, hg0⟩ : ∃ g0, g0 = C.ι γ := ⟨_, rfl⟩
  rw [← hg0] at he
  obtain ⟨h1, h2⟩ := fin_uniq f (B.bG g0) k k' hk hk' (hγ.symm.trans he)
  subst h2
  rw [h1, map_mul, MulEquiv.symm_apply_apply, hg0, hψ.1, hW, inf_eq B j γ k hτ]

private theorem level_step (B : Bridge L) (A : SD B.Δ) (S : Finset (Plc L)) (VL : ∀ w : Plc L, Lev (Kw w))
    (hlG : ∀ g : GA B.Δ, g ∈ A.dat.UG ↔ (B.bG g : UA L 3) ∈ lev (Kall L 3) S VL) (j : ℕ) (ch : Lp L → ℂ)
    (C : Base (U3 B.Δ) (GA B.Δ) (Wt.VG (InfinitePlace L) j)) (s : C.Tw) (hBG : A.dat.IsBG ch C s)
    (ψ : GA B.Δ → Wt.VG (InfinitePlace L) j) (hψ : ψ ∈ C.Forms)
    (u : finU L 3) (hu : (u : UA L 3) ∈ lev (Kall L 3) S VL) (g : finU L 3) :
    ψ (B.bG.symm (g * u)) = ψ (B.bG.symm g) := by
  have hm : B.bG.symm u ∈ C.U := by
    rw [hBG.U, hlG, MulEquiv.apply_symm_apply]
    exact hu
  have h1 := hψ.2 (B.bG.symm g) ⟨_, hm⟩
  rw [map_mul]
  rw [hBG.ω] at h1
  simpa using h1

private def pull {B : Bridge L} (T : Spl B) (w : Plc L) (h : IsSplitAt w) (d : Fin 3 → (Kw w)ˣ) :
    Fin 3 → (Kv (un w))ˣ := fun i => Units.map ((T w h).i.symm : Kw w →* Kv (un w)) (d i)

open Classical in
private def ddf {B : Bridge L} (T : Spl B) (w : Plc L) (h : IsSplitAt w) (d : Fin 3 → (Kw w)ˣ) :
    ParN (Lp L) 3 := Function.update 1 (un w) (pull T w h d)

private theorem iu_pull {B : Bridge L} (T : Spl B) (w : Plc L) (h : IsSplitAt w) (d : Fin 3 → (Kw w)ˣ) (i : Fin 3) :
    iu T w h (pull T w h d i) = d i := by
  refine Units.ext ?_
  simp [pull, iu]

private theorem ddf_self {B : Bridge L} (T : Spl B) (w : Plc L) (h : IsSplitAt w) (d : Fin 3 → (Kw w)ˣ) :
    ddf T w h d (un w) = pull T w h d := by
  simp [ddf]

open Classical in
private theorem ddf_ne {B : Bridge L} (T : Spl B) (w : Plc L) (h : IsSplitAt w) (d : Fin 3 → (Kw w)ˣ)
    {v : Pl (Lp L)} (hv : v ≠ un w) : ddf T w h d v = 1 := by
  simp [ddf, Function.update_of_ne hv]

private theorem is_el {B : Bridge L} (T : Spl B) (S : Finset (Plc L)) (A : SD B.Δ)
    (hEl : ∀ (g : GA B.Δ) d, A.IsElG g d ↔ OnS S (B.bG g : UA L 3) ∧ ∀ w ∈ S, ∀ h, cLoc w (B.bG g : UA L 3) = Sig.dg fun i => iu T w h (d (un w) i))
    (hpl : Places (S : Set (Plc L))) (w : Plc L) (hw : w ∈ S) (h : IsSplitAt w) (d : Fin 3 → (Kw w)ˣ)
    (x : finU L 3) (hx : (x : UA L 3) = secW 3 w (Sig.dg d)) : A.IsElG (B.bG.symm x) (ddf T w h d) := by
  obtain ⟨hsec, -⟩ := Br.uaFacts L 3
  have hloc := (hsec w h).1 (Sig.dg d)
  have hc := (hsec w h).2.1 (Sig.dg d)
  rw [← hx] at hloc hc
  have hoff : ∀ u, un u ≠ un w → cLoc u (x : UA L 3) = 1 := fun u hu =>
    MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hloc.2 u) hu)
  rw [hEl, MulEquiv.apply_symm_apply]
  refine ⟨⟨x.2, fun u hu => hoff u (hu w hw)⟩, fun w' hw' h' => ?_⟩
  by_cases hww : w' = w
  · subst hww
    rw [hc]
    have e : (fun i => iu T w' h' (ddf T w' h d (un w') i)) = d :=
      funext fun i => by rw [ddf_self]; exact iu_pull T w' h d i
    rw [e]
  · have hne : un w' ≠ un w := fun e => hww (hpl.inj (by exact_mod_cast hw') (by exact_mod_cast hw) e)
    rw [hoff w' hne]
    have e : (fun i => iu T w' h' (ddf T w h d (un w') i)) = 1 :=
      funext fun i => by rw [ddf_ne T w h d hne]; simp
    rw [e]
    simp

private theorem dom_ddf {B : Bridge L} (T : Spl B) (A : SD B.Δ) (w : Plc L) (h : IsSplitAt w) (d : Fin 3 → (Kw w)ˣ)
    (hd : Sig.SDom d) : A.DomS (ddf T w h d) := by
  intro v _
  by_cases hv : v = un w
  · subst hv
    rw [ddf_self]
    intro i k hik
    rcases hik.lt_or_eq with h1 | rfl
    · refine ((T w h).val_le _ _).1 ?_
      have e : ∀ i, (T w h).i ((pull T w h d i : (Kv (un w))ˣ) : Kv (un w)) = (d i : Kw w) := fun i =>
        congrArg Units.val (iu_pull T w h d i)
      rw [e, e]
      exact (hd i k h1).le
    · exact le_rfl
  · rw [ddf_ne T w h d hv]
    intro i k _
    simp

private theorem ex_ddf {B : Bridge L} (T : Spl B) (S : Finset (Plc L)) (VL : ∀ w : Plc L, Lev (Kw w)) (A : SD B.Δ)
    (hF : Fit T S VL A) (a : ∀ w : Plc L, (Kw w)ˣ →* ℂˣ) (b : Chs (Lp L)) (hab : FitCh T S a b)
    (hEx : ∀ w (h : IsSplitAt w) (n : ℕ) (ψ : Fin n → (Kw w)ˣ →* ℂˣ) (d : Fin n → (Kv (un w))ˣ), n = 2 ∨ n = 3 →
      expo ψ (fun i => iu T w h (d i)) = expo (fun i => (ψ i).comp (iu T w h)) d)
    (w : Plc L) (hw : w ∈ S) (h : IsSplitAt w) (d : Fin 3 → (Kw w)ˣ) :
    A.exG b (ddf T w h d) = expo ![a w, 1, (a w)⁻¹] d := by
  have hmem : un w ∈ A.Sg := (hF.sg _).2 ⟨w, hw, rfl⟩
  unfold SD.exG
  rw [Finset.prod_eq_single_of_mem (un w) hmem]
  · rw [ddf_self, hab w hw h]
    have e1 := hEx w h 3 ![a w, 1, (a w)⁻¹] (pull T w h d) (Or.inr rfl)
    have e2 : (fun i => iu T w h (pull T w h d i)) = d := funext (iu_pull T w h d)
    rw [e2] at e1
    rw [e1]
    congr 1
    funext i
    fin_cases i <;> rfl
  · intro v _ hv
    rw [ddf_ne T w h d hv]
    exact ((So.expoEq (Kv v) (b v)).2.2 3 _).2.1

private theorem dc_step {G G' V : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V] (e : G ≃* G')
    (U' : Subgroup G') (U : Subgroup G) (hU : U'.comap e.toMonoidHom = U) (ψ : G → V) (g : G) (c : ℂ)
    (hfo : UpperTheory.V.AlgebraTools.FinOrb U' U' (e g)) (hlev : ∀ u ∈ U', ∀ x, ψ (e.symm (x * u)) = ψ (e.symm x))
    (h : dcF U g ψ = c • ψ) : dcF U' (e g) (ψ ∘ e.symm) = c • (ψ ∘ e.symm) := by
  have t := (So.dcMap G G' V e.toMonoidHom e.bijective U' g g).2.2.2 hfo (ψ ∘ e.symm) hlev
  have e1 : (ψ ∘ e.symm) ∘ e.toMonoidHom = ψ := funext fun y => by simp
  rw [e1, hU, h] at t
  funext y
  have := congrFun t (e.symm y)
  simpa using this.symm

private theorem lev_G (B : Bridge L) (hB : B.Ok) (T : Spl B) (S : Finset (Plc L)) (VL : ∀ w : Plc L, Lev (Kw w)) (A : SD B.Δ)
    (hA : A.Ok) (hF : Fit T S VL A) : ∀ g : GA B.Δ, g ∈ A.dat.UG ↔ (B.bG g : UA L 3) ∈ lev (Kall L 3) S VL :=
  (So.levG L B hB T S VL A hA hF).1

private theorem lev_El (B : Bridge L) (hB : B.Ok) (T : Spl B) (S : Finset (Plc L)) (VL : ∀ w : Plc L, Lev (Kw w)) (A : SD B.Δ)
    (hA : A.Ok) (hF : Fit T S VL A) : ∀ (g : GA B.Δ) d, A.IsElG g d ↔ OnS S (B.bG g : UA L 3) ∧ ∀ w ∈ S, ∀ h, cLoc w (B.bG g : UA L 3) = Sig.dg fun i => iu T w h (d (un w) i) :=
  (So.levG L B hB T S VL A hA hF).2.2.1

private theorem lev_Ex (B : Bridge L) (hB : B.Ok) (T : Spl B) (S : Finset (Plc L)) (VL : ∀ w : Plc L, Lev (Kw w)) (A : SD B.Δ)
    (hA : A.Ok) (hF : Fit T S VL A) : ∀ w (h : IsSplitAt w) (n : ℕ) (ψ : Fin n → (Kw w)ˣ →* ℂˣ) (d : Fin n → (Kv (un w))ˣ), n = 2 ∨ n = 3 →
      expo ψ (fun i => iu T w h (d i)) = expo (fun i => (ψ i).comp (iu T w h)) d :=
  (So.levG L B hB T S VL A hA hF).2.2.2.2

private theorem eig_fin (B : Bridge L) (T : Spl B) (S : Finset (Plc L)) (VL : ∀ w : Plc L, Lev (Kw w)) (A : SD B.Δ)
    (hF : Fit T S VL A)
    (hlG : ∀ g : GA B.Δ, g ∈ A.dat.UG ↔ (B.bG g : UA L 3) ∈ lev (Kall L 3) S VL)
    (hEl : ∀ (g : GA B.Δ) d, A.IsElG g d ↔ OnS S (B.bG g : UA L 3) ∧ ∀ w ∈ S, ∀ h, cLoc w (B.bG g : UA L 3) = Sig.dg fun i => iu T w h (d (un w) i))
    (hEx : ∀ w (h : IsSplitAt w) (n : ℕ) (ψ : Fin n → (Kw w)ˣ →* ℂˣ) (d : Fin n → (Kv (un w))ˣ), n = 2 ∨ n = 3 →
      expo ψ (fun i => iu T w h (d i)) = expo (fun i => (ψ i).comp (iu T w h)) d)
    (j : ℕ) (ch : Lp L → ℂ) (C : Base (U3 B.Δ) (GA B.Δ) (Wt.VG (InfinitePlace L) j)) (s : C.Tw) (hBG : A.dat.IsBG ch C s)
    (ψ : GA B.Δ → Wt.VG (InfinitePlace L) j) (hψ : ψ ∈ C.Forms)
    (a : ∀ w : Plc L, (Kw w)ˣ →* ℂˣ) (b : Chs (Lp L)) (hab : FitCh T S a b) (hE : A.EigG ψ b)
    (w : Plc L) (hw : w ∈ S) (h : IsSplitAt w) (d : Fin 3 → (Kw w)ˣ) (hd : Sig.SDom d)
    (x : finU L 3) (hx : (x : UA L 3) = secW 3 w (Sig.dg d))
    (hfo : UpperTheory.V.AlgebraTools.FinOrb ((lev (Kall L 3) S VL).subgroupOf (finU L 3)) ((lev (Kall L 3) S VL).subgroupOf (finU L 3)) x) :
    dcF ((lev (Kall L 3) S VL).subgroupOf (finU L 3)) x (fun y => ψ (B.bG.symm y)) =
      expo ![a w, 1, (a w)⁻¹] d • (fun y => ψ (B.bG.symm y)) := by
  have hg := is_el T S A hEl hF.pl w hw h d x hx
  have hcomap : ((lev (Kall L 3) S VL).subgroupOf (finU L 3)).comap B.bG.toMonoidHom = A.dat.UG := by
    ext g
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hlG]
    rfl
  have hE' := hE _ _ (dom_ddf T A w h d hd) hg
  rw [ex_ddf T S VL A hF a b hab hEx w hw h d] at hE'
  have hfo2 : UpperTheory.V.AlgebraTools.FinOrb ((lev (Kall L 3) S VL).subgroupOf (finU L 3)) ((lev (Kall L 3) S VL).subgroupOf (finU L 3)) (B.bG (B.bG.symm x)) := by
    rw [MulEquiv.apply_symm_apply]
    exact hfo
  have hstep := dc_step B.bG ((lev (Kall L 3) S VL).subgroupOf (finU L 3)) A.dat.UG hcomap ψ (B.bG.symm x) _ hfo2
    (fun u hu g => level_step B A S VL hlG j ch C s hBG ψ hψ u (Subgroup.mem_subgroupOf.1 hu) g) hE'
  rw [MulEquiv.apply_symm_apply] at hstep
  exact hstep

end

theorem UpperTheory.V.Z.Sym.So.outG :
    UpperTheory.V.Z.Sym.So.OutG := by
  intro L _ _ _ B hB T S VL A hA hF j a b hab ch C s hBG hW ψ hψ hne hE
  have hsec := (Br.uaFacts L 3).1
  have hlG := lev_G B hB T S VL A hA hF
  have hEl := lev_El B hB T S VL A hA hF
  have hExpo := lev_Ex B hB T S VL A hA hF
  have hU : lev (Kall L 3) S VL ≤ finU L 3 := inf_le_left.trans inf_le_left
  have hf := So.finToAF L 3 (Wt.VG (InfinitePlace L) j) (Wt.repG _ j) _ hU (fun x => ψ (B.bG.symm x))
    (fun f k hk hfk g => left_step B hB A j ch C s hBG hW ψ hψ f k hk hfk g)
    (fun u hu g => level_step B A S VL hlG j ch C s hBG ψ hψ u hu g)
  obtain ⟨φ, hAF, hφ, hdc⟩ := hf
  refine ⟨φ, ?_, hAF, ?_⟩
  · intro h0
    refine hne (funext fun g => ?_)
    have h1 := hφ (B.bG g)
    rw [h0] at h1
    simpa using h1.symm
  · intro w hw d hd
    have h := hF.pl.split w hw
    have hx0 : secW 3 w (Sig.dg d) ∈ finU L 3 := ((hsec w h).1 _).1
    have hat := So.dcAt L 3 (Kall L 3) S VL hF.pl w hw ⟨le_rfl, fun _ _ => inf_le_right⟩ d
    have hfo := hat.1
    refine (hat.2 _ φ hAF.level _).2 ?_
    exact hdc ⟨_, hx0⟩ _ hfo (eig_fin B T S VL A hF hlG hEl hExpo j ch C s hBG ψ hψ a b hab hE w hw h d hd ⟨_, hx0⟩ rfl
      (finOrb_sub _ _ (⟨_, hx0⟩ : finU L 3) hfo))

end
