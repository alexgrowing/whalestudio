import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.TiedTwJSym
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSmulMemOfMemLocW

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.FormSym

theorem mem_FiC_comp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    {ι : Type} [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (lam : ι → DomWeight n)
    {c c' : Type} (yc : c → UPts σ J (FiniteAdeleRing (𝓞 F) F)) (e : c' → c) (he : Function.Surjective e)
    (g : c → Frames (gramC J emb) → ℂ) :
    g ∘ e ∈ FiC S emb lam (yc ∘ e) ↔ g ∈ FiC S emb lam yc := by
  simp only [FiC, Submodule.mem_map]
  constructor
  · rintro ⟨h, hh, he'⟩
    refine ⟨h, hh, ?_⟩
    funext x
    obtain ⟨x', rfl⟩ := he x
    exact congrFun he' x'
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩

section Gen

variable {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m} {Ch : Type} {chOf : (D.mem u).C.cls i → Ch}

def clsOfChart (β : Ch) (hβ : ∀ c, chOf c = β)
    (K : LevelChart D (D.mem u).A.T (badG D) i hi (fun c : {c // chOf c = β} => (D.mem u).C.stab i c.1)
      (fun c => clsCrd D u i hi c.1)) : ClsTied u i hi where
  lev := K.lev
  y c := K.y ⟨c, hβ c⟩
  y_bij := K.y_bij.comp (f := fun c : (D.mem u).C.cls i => (⟨c, hβ c⟩ : {c // chOf c = β}))
    ⟨fun _ _ h => congrArg Subtype.val h, fun c => ⟨c.1, rfl⟩⟩
  y_lat c := K.y_lat ⟨c, hβ c⟩
  stabI c := K.stabI ⟨c, hβ c⟩
  stabI_inj c := K.stabI_inj ⟨c, hβ c⟩
  stabI_range c := K.stabI_range ⟨c, hβ c⟩

set_option maxHeartbeats 4000000 in

def valOfG [Subsingleton Ch] (eV : (D.mem u).A.vT ≃ PlT D u)
    (K : ∀ β : Ch, LevelChart D (D.mem u).A.T (badG D) i hi (fun c : {c // chOf c = β} => (D.mem u).C.stab i c.1)
      (fun c => clsCrd D u i hi c.1)) (β : Ch) (hβ : ∀ c, chOf c = β)
    (eY : (D.mem u).C.Y i ≃ Fr D i hi)
    (hde : ∃ C : GL (Fin (D.R.N i)) D.host.E,
      cT (sigD D : D.host.E →+* D.host.E) C.1 * C.1 = gramN D i hi ∧
      (∀ x : Fin (D.R.N i) → D.host.E, x ∈ selfDualLatticeCoords D i hi ↔ ∀ a, (C.1 *ᵥ x) a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) ∧
      ∀ τ z, (D.mem u).C.de i z τ = embT D τ C.1.det * ((eY z).1 τ).det)
    (hV : ValuationCompatibleChart (D.fm u) eY (fun _ => True) chOf (lat := fun c => clsCrd D u i hi c) K)
    (hI : IpVTieG (D.fm u) eY)
    (hD : DilationCompatibleChart (D.fm u) eY eV chOf (lat := fun c => clsCrd D u i hi c) K) :
    ValTied u eV i hi (clsOfChart β hβ (K β)) where
  eY := eY
  de := hde
  Fi φ := by
    rw [hV.Fi φ]
    constructor
    · intro h
      exact (mem_FiC_comp _ _ _ (K β).y (fun c => (⟨c, hβ c⟩ : {c // chOf c = β})) (fun c => ⟨c.1, rfl⟩) _).2 (h β)
    · intro h β'
      obtain rfl : β = β' := Subsingleton.elim _ _
      exact (mem_FiC_comp _ _ _ (K β).y (fun c => (⟨c, hβ c⟩ : {c // chOf c = β})) (fun c => ⟨c.1, rfl⟩) _).1 h
  ipV := hI
  rat := hV.rat
  lat x := by
    constructor
    · intro hx w
      exact (hV.lat w trivial x).1 (Submodule.subset_span hx)
    · intro h
      exact GlobalTheory.LvT.mem_of_forall_locW D _ (fun w => (hV.lat w trivial x).2 (h w))
  dil v a k hk c δ hδ := hD.dil v a k hk β ⟨c, hβ c⟩ δ hδ
  dilT v a k hk c δ hδ g hg := hD.dilT v a k hk β ⟨c, hβ c⟩ δ hδ g hg

set_option maxHeartbeats 4000000 in

def lvOfG (A : AtTTied u) (L : LevelCompatibleLattices (D.fm u) (D.mem u).A.T A.res i hi (fun c => clsCrd D u i hi c)) :
    LvTied u A i hi where
  pr := L.pr
  pr_surj := L.pr_surj
  pr_smul := L.pr_smul
  pr_ker := L.pr_ker
  fv_ker := L.fv_ker
  prk := L.prk
  prk_surj := L.prk_surj
  prk_smul := L.prk_smul
  prk_ker := L.prk_ker
  te := L.te

variable (A : AtTTied u) (L : LevelCompatibleLattices (D.fm u) (D.mem u).A.T A.res i hi (fun c => clsCrd D u i hi c))
  (K : ∀ β : Ch, LevelChart D (D.mem u).A.T (badG D) i hi (fun c : {c // chOf c = β} => (D.mem u).C.stab i c.1)
      (fun c => clsCrd D u i hi c.1)) (β : Ch) (hβ : ∀ c, chOf c = β)

set_option maxHeartbeats 4000000 in
theorem fvOfG (fMe : ∀ β v, (K β).lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v) (h : FvTieG L A.eV K fMe) :
    FvTie (lvOfG A L) (clsOfChart β hβ (K β)) (fMe β) :=
  fun v c z hz => h v β ⟨c, hβ c⟩ z hz

set_option maxHeartbeats 4000000 in
theorem upOfG (eY : (D.mem u).C.Y i ≃ Fr D i hi) (W : ValTied u A.eV i hi (clsOfChart β hβ (K β))) (hY : W.eY = eY)
    (h : UpNatTieG L eY A.eV K) : UpNatTie (lvOfG A L) (clsOfChart β hβ (K β)) W := by
  intro v c z hz
  obtain ⟨_, γ, η, κ, h1, h2, h3, h4, h5, h6⟩ := h v β ⟨c, hβ c⟩ z hz
  refine ⟨γ, η, κ, h1, h2, h3, h4, h5, fun g s s' hs => ?_⟩
  rw [hY] at hs
  exact h6 g s s' hs

set_option maxHeartbeats 4000000 in
theorem dnOfG (eY : (D.mem u).C.Y i ≃ Fr D i hi) (W : ValTied u A.eV i hi (clsOfChart β hβ (K β))) (hY : W.eY = eY)
    (h : DnNatTieG L eY A.eV K) : DnNatTie (lvOfG A L) (clsOfChart β hβ (K β)) W := by
  intro v c g hg
  obtain ⟨_, γ, η, κ, h1, h2, h3, h4, h6⟩ := h v β ⟨c, hβ c⟩ g hg
  refine ⟨γ, η, κ, h1, h2, h3, h4, fun f s s' hs => ?_⟩
  rw [hY] at hs
  exact h6 f s s' hs

end Gen

section Gen2

variable {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m}

set_option maxHeartbeats 4000000 in
theorem normOfG {eV : (D.mem u).A.vT ≃ PlT D u} {K : ClsTied u i hi} (eY : (D.mem u).C.Y i ≃ Fr D i hi)
    (W : ValTied u eV i hi K) (hY : W.eY = eY) (h : NormTieG (D.fm u) eY) : NormTie W := by
  intro s x Pc hPc o ho
  rw [hY] at hPc
  exact h s x Pc hPc o ho

set_option maxHeartbeats 4000000 in
theorem bwOfG (A : AtTTied u) {K : ClsTied u i hi} (eY : (D.mem u).C.Y i ≃ Fr D i hi)
    (W : ValTied u A.eV i hi K) (hY : W.eY = eY)
    (h : BwTieG (D.fm u) (D.mem u).A.T A.res eY (fun c => clsCrd D u i hi c)) : BwTie A W := by
  intro w hw hs v x
  rw [hY]
  exact h w hw hs v x

end Gen2

set_option maxHeartbeats 4000000 in

theorem readsK_one {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {u : B.Word} {a : I.ι}
    {i : ℕ} {hi : i ≤ B.R.m} {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {Ch : Type} {chOf : (I.stp u a i).Cl → Ch}
    {K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
      (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))} (h : I.ReadsK l Z u a i hi chOf K) (β : Ch)
    (hβ : ∀ c, chOf c = β) :
    ∃ k, I.Reads u a i (fun _ => ()) (fun _ => (K β).lev.Lb) (fun _ => (K β).lev.U) (fun _ => (K β).lev.chi)
      (fun c => ((K β).y ⟨c, hβ c⟩).1) (fun c s => ((K β).stabI ⟨c, hβ c⟩ s).1) k := by
  obtain rfl : chOf = fun _ => β := funext hβ
  obtain ⟨k, hk⟩ := h
  refine ⟨fun _ => k β, ⟨fun c c' => ⟨fun _ => (hk.key c c').1 rfl, fun _ => rfl⟩, fun _ => ?_, fun _ => hk.lb β,
    fun _ => hk.k_std β, fun _ => hk.k_off β, fun _ => hk.k_T β, hk.pt, hk.lev, hk.chr, hk.stab⟩⟩
  obtain ⟨c, _⟩ := hk.onto β
  exact ⟨c, rfl⟩

end GlobalTheory.Mem.FormSym

end
