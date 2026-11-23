import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting.MtIndep

section rep
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem isoRep_trans {W₁ W₂ W₃ : Type} [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]
    [AddCommGroup W₃] [Module ℂ W₃] {S₁ : Submodule ℂ (GAf L n → W₁)} {S₂ : Submodule ℂ (GAf L n → W₂)}
    {S₃ : Submodule ℂ (GAf L n → W₃)} (h₁ : NG.IsoRep S₁ S₂) (h₂ : NG.IsoRep S₂ S₃) : NG.IsoRep S₁ S₃ := by
  obtain ⟨T, hT⟩ := h₁
  obtain ⟨U, hU⟩ := h₂
  exact ⟨T.trans U, fun h f f' e => hU h (T f) (T f') (hT h f f' e)⟩

theorem isoRep_symm {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ (GQ L n) W} {S₁ : Submodule ℂ (GAf L n → W)} {S₂ : Submodule ℂ (GAf L n → W')}
    (hs : NG.IsSubrep ρ S₁) (h : NG.IsoRep S₁ S₂) : NG.IsoRep S₂ S₁ := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T.symm, fun h g g' e => ?_⟩
  have hm : NG.rt L n h ((T.symm g : S₁) : GAf L n → W) ∈ S₁ := hs.stable h _ (T.symm g).2
  have key := hT h (T.symm g) ⟨_, hm⟩ rfl
  rw [LinearEquiv.apply_symm_apply] at key
  have hg : T ⟨_, hm⟩ = g' := Subtype.ext (key.trans e.symm)
  rw [← hg, LinearEquiv.symm_apply_apply]

theorem isoTyp_eq {W : Type} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (GQ L n) W}
    {S₁ S₂ : Submodule ℂ (GAf L n → W)} (hs : NG.IsSubrep ρ S₁) (h : NG.IsoRep S₁ S₂) :
    NG.isoTyp ρ S₁ = NG.isoTyp ρ S₂ := by
  unfold NG.isoTyp
  congr 1
  ext S'
  simp only [Set.mem_setOf_eq]
  exact and_congr_right fun _ => ⟨fun h' => isoRep_trans (isoRep_symm hs h) h', fun h' => isoRep_trans h h'⟩

end rep

section loc
variable {D : D7}

def BCd (X : LocNd (lay0 D)) (Y : LocAut X) (Pa : List (Part Y.naut.CG)) (loc : ∀ w, Y.naut.LP w)
    (sat : PlE D.host → Multiset ℂ) (inf : (D.host.E →+* ℂ) → Multiset ℂ) : Prop :=
  (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ Y.naut.csd p.π) ∧
  (Pa.map fun p => ((⟨p.a, p.π⟩ : Σ a, Y.naut.CG a), p.d)).Nodup ∧
  rankIso X.nd Y.naut Pa = D.R.nV ∧
  (∀ w, IsSplitPl D.host w → isoLoc X.nd Y.naut Pa w = loc w) ∧
  (∀ w, ¬ IsSplitPl D.host w → Y.naut.unr (isoLoc X.nd Y.naut Pa w) ∧
    Y.naut.frobEig (isoLoc X.nd Y.naut Pa w) = ubc D.R.nV (sat w)) ∧
  ∀ τ, isoInf X.nd Y.naut Pa τ = inf τ

def Good (X : LocNd (lay0 D)) (Y : LocAut X) (σ' : D.ntypes.Par) (c : Y.naut.CG 1) (j : ℕ) (u : D.nbc.AU j) : Prop :=
  ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = D.ntypes.locPar σ' w) ∧
    BCd X Y (twistIso X.nd Y.naut (Sig ++ [⟨1, c, D.R.t⟩]) Y.naut.etaTinv) (fun w => D.nbc.locAU j u w)
      (D.nbc.satAU j u) (D.nbc.infW j (D.nbc.wtAU j u))

def Phi {cf : CharFrame D} {jE : D.host.E →+* Qb} (X : LocNd (lay0 D)) (Y : LocAut X) (A : SideA D cf jE) (M : MtFam D)
    (σ' : D.ntypes.Par) (c : Y.naut.CG 1) (μ : D.what₂.Tup) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    Submodule ℂ (D.what₂.Mt μ j) :=
  ⨆ (S' : Submodule ℂ (GAf D.host.E D.R.nV → (M μ j h1 h2).wt.W)) (h : NG.IsIrrRep (M μ j h1 h2).wt.ρ S')
    (_ : Good X Y σ' c j (A.au.cls j h1 h2 { (M μ j h1 h2).wt with S := S', irrS := h })),
    (NG.isoTyp (M μ j h1 h2).wt.ρ S').comap (M μ j h1 h2).real

theorem phi_heq {cf : CharFrame D} {jE : D.host.E →+* Qb} (X : LocNd (lay0 D)) (Y : LocAut X) (A : SideA D cf jE)
    (M : MtFam D) (σ' : D.ntypes.Par) (c : Y.naut.CG 1) {μ μ' : D.what₂.Tup} {j j' : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (h1' : 1 ≤ j') (h2' : j' ≤ D.R.m) (hμ : μ = μ') (hj : j = j') :
    HEq (Phi X Y A M σ' c μ j h1 h2) (Phi X Y A M σ' c μ' j' h1' h2') := by
  subst hμ hj; rfl

end loc

end GlobalTheory.HeightCounting.MtIndep

namespace GlobalTheory.HeightCounting.MtIndep

section loc2
variable {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {M : MtFam D}
  {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {X : LocNd (lay0 D)}
  {iq : ∀ i : X.nd.Loc, FractionRing (X.nd.O i) →+* Qbar (X.nd.l i)} {Y : LocAut X} {Cb : LocBC Y}

theorem iSup_eq_phi (hS : AutSpec A M tup iq Y Cb) (σ' : D.ntypes.Par) (i : X.nd.Loc) :
    (⨆ P ∈ {P | ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = D.ntypes.locPar σ' w) ∧ IsBCV X.nd Y.naut i P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i]) Y.naut.etaTinv)}, Y.naut.typeV i P) =
    Phi X Y A M σ' (Y.muC i) (X.nd.mu i) (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 := by
  have hc : ∀ P, (∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = D.ntypes.locPar σ' w) ∧ IsBCV X.nd Y.naut i P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i]) Y.naut.etaTinv)) ↔
      Good X Y σ' (Y.muC i) (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2
        { (mlX M X i).wt with S := hS.S i P, irrS := hS.irr i P }) := by
    intro P
    have hl : Y.naut.locV i P = fun w => D.nbc.locAU (X.nd.j i) (Cb.embAV i P) w := funext (Cb.embAV_loc i P)
    have hs : Y.naut.satV i P = D.nbc.satAU (X.nd.j i) (Cb.embAV i P) := funext (Cb.embAV_sat i P)
    have hf : Y.naut.infWt i = D.nbc.infW (X.nd.j i) (D.nbc.wtAU (X.nd.j i) (Cb.embAV i P)) := Cb.embAV_inf i P
    rw [← hS.emb i P]
    unfold Good
    refine exists_congr fun Sig => and_congr_right fun _ => ?_
    unfold IsBCV BCd
    rw [hl, hs, hf]
    exact Iff.rfl
  apply le_antisymm
  · refine iSup₂_le fun P hP => ?_
    rw [hS.typeV i P]
    exact le_iSup_of_le (hS.S i P) (le_iSup_of_le (hS.irr i P) (le_iSup_of_le ((hc P).1 hP) le_rfl))
  · refine iSup_le fun S' => iSup_le fun hirr => iSup_le fun hg => ?_
    by_cases hb : (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real = ⊥
    · exact hb.le.trans bot_le
    · obtain ⟨P, hP⟩ := hS.surj i S' hirr hb
      have ht : Y.naut.typeV i P = (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real := by
        rw [hS.typeV i P, isoTyp_eq (hS.irr i P).1 hP]
      have hcl : A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2
            { (mlX M X i).wt with S := hS.S i P, irrS := hS.irr i P } =
          A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2
            { (mlX M X i).wt with S := S', irrS := hirr } :=
        (A.au.iso _ _ _ _ _).2 ⟨⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩, hP⟩
      have hP' : P ∈ {P | ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = D.ntypes.locPar σ' w) ∧ IsBCV X.nd Y.naut i P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i]) Y.naut.etaTinv)} :=
        (hc P).2 (hcl ▸ hg)
      exact le_iSup₂_of_le (f := fun P _ => Y.naut.typeV i P) P hP' ht.ge

end loc2

theorem typeV_iSup_indep : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T), ∀ (Y : LocAut X) (Cb : LocBC Y), AutSpec A M tp.tup Sp.iq Y Cb → ∀ (i i' : X.nd.Loc) (σ' : D.ntypes.Par), X.nd.mu i = X.nd.mu i' → X.nd.j i = X.nd.j i' → HEq (⨆ P ∈ {P | ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = D.ntypes.locPar σ' w) ∧ IsBCV X.nd Y.naut i P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i]) Y.naut.etaTinv)}, Y.naut.typeV i P) (⨆ P ∈ {P | ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = D.ntypes.locPar σ' w) ∧ IsBCV X.nd Y.naut i' P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i']) Y.naut.etaTinv)}, Y.naut.typeV i' P) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp _ _ _ _ _ _ big X T Sp Y Cb hS i i' σ' hmu hj
  rw [iSup_eq_phi hS σ' i, iSup_eq_phi hS σ' i']
  have hc : Y.muC i = Y.muC i' := by
    obtain ⟨h1, h2⟩ := X.nd.j_range i
    have e := hS.muC i ⟨X.nd.j i - 1, by omega⟩ (by simp only; omega)
    have e' := hS.muC i' ⟨X.nd.j i - 1, by omega⟩ (by simp only; omega)
    rw [hmu] at e
    exact A.chr.e1.injective (Subtype.ext (e.trans e'.symm))
  rw [hc]
  exact phi_heq X Y A M σ' _ _ _ _ _ hmu hj

end GlobalTheory.HeightCounting.MtIndep
