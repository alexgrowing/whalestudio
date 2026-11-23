import Formalism.LocalToGlobal.GroupLattices.LevelCharts.LevelsOfChChartsCover

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.MainNotions.G.ChartsLv

open Formalism.L2.G

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
  {L : ColLevel R F E sp gp C A clsLat} {p : ℕ} {G : GAtP p}

structure ChartG (X : Formalism.L2.Herm.GLevTie L G) (N : ℕ) where
  J : Matrix (Fin N) (Fin N) E
  Lb : Submodule (𝓞 E) (Fin N → E)
  Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F))
  fr : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal → GL (Fin N) (w.adicCompletion F)
  fr_lat : ∀ w h (t : Fin N → w.adicCompletion F),
    (∃ x ∈ Formalism.L2.Herm.locL w Lb, ∀ a, (X.spl w h (x a)).1 = t a) ↔
      ∀ a, (((fr w h)⁻¹ : GL (Fin N) (w.adicCompletion F)) :
        Matrix (Fin N) (Fin N) (w.adicCompletion F)).mulVec t a ∈ w.adicCompletionIntegers F
  ψ : awayG sp.cm.sig J Uloc p →* G.Oˣ
  eps : UJ (sp.cm.sig : E →+* E) J →* G.Oˣ
  fin : Finite (compG sp.cm.sig J Uloc p)

namespace ChartG

variable {X : Formalism.L2.Herm.GLevTie L G} {N : ℕ} (St : ChartG X N)

abbrev Up : Subgroup (GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := awayG sp.cm.sig St.J St.Uloc p

abbrev comp : Type := compG sp.cm.sig St.J St.Uloc p

abbrev rep (i : St.comp) : UPts sp.cm.sig St.J (FiniteAdeleRing (𝓞 F) F) := repG sp.cm.sig St.J St.Uloc p i

abbrev Gam (i : St.comp) : Subgroup (UJ (sp.cm.sig : E →+* E) St.J) :=
  gamC sp.cm.sig St.J St.Up (St.rep i : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))

def actW (i : St.comp) (v : Fin G.P.nV) : St.Gam i →* GL (Fin N) ((X.pl v).1.adicCompletion F) :=
  (MulAut.conj (St.fr (X.pl v).1 (X.pl v).2)⁻¹).toMonoidHom.comp
    ((bc ((RingHom.fst _ _).comp (X.spl (X.pl v).1 (X.pl v).2).toRingHom)).comp
      ((bc (inclE (F := F) ((X.pl v).1.adicCompletion F))).comp
        (gamMat sp.cm.sig St.J St.Up (St.rep i : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))))

theorem actW_apply (i : St.comp) (v : Fin G.P.nV) (γ : St.Gam i) :
    St.actW i v γ = (St.fr (X.pl v).1 (X.pl v).2)⁻¹ * bc ((RingHom.fst _ _).comp (X.spl (X.pl v).1 (X.pl v).2).toRingHom)
      (bc (inclE (F := F) ((X.pl v).1.adicCompletion F)) ((γ : UJ (sp.cm.sig : E →+* E) St.J) : GL (Fin N) E)) *
        St.fr (X.pl v).1 (X.pl v).2 := by
  show (MulAut.conj (St.fr (X.pl v).1 (X.pl v).2)⁻¹) _ = _
  rw [MulAut.conj_apply, inv_inv]
  rfl

end ChartG

def levG {X : Formalism.L2.Herm.GLevTie L G} (Fl : Fills G) (i : ℕ) {N : ℕ} (hk : G.P.m + (i + 1) * (Fl.t + 1) + 1 = N) (St : ChartG X N)
    (c : St.comp) : Level (Fl.Pj (i + 1)) where
  Γ := St.Gam c
  act := fun (v : Fin G.P.nV) => (castGL hk (G.P.Qq v)).symm.toMonoidHom.comp
    ((bc (X.eQ v _ rfl).symm.toRingHom).comp (St.actW c v))
  χ := St.ψ.comp (gamToUp sp.cm.sig St.J St.Up (St.rep c : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) *
      St.eps.comp (St.Gam c).subtype

def levelsG (X : Formalism.L2.Herm.GLevTie L G) (Fl : Fills G) (M : ℕ) (Nj : ℕ → ℕ)
    (hN : ∀ i, i < M → G.P.m + (i + 1) * (Fl.t + 1) + 1 = Nj i) (Ch : ∀ i, i < M → Type) [∀ i h, Finite (Ch i h)]
    (St : ∀ i (h : i < M), Ch i h → ChartG X (Nj i)) : Levels Fl where
  compS := fun i => (h : i < M) ×' Σ b : Ch i h, (St i h b).comp
  finS := fun i => by
    haveI : ∀ (h : i < M) (b : Ch i h), Finite (St i h b).comp := fun h b => (St i h b).fin
    exact Fintype.ofFinite _
  levS := fun i c => levG Fl i (hN i c.1) (St i c.1 c.2.1) c.2.2

variable (X : Formalism.L2.Herm.GLevTie L G) (Fl : Fills G) (M : ℕ) (Nj : ℕ → ℕ)
    (hN : ∀ i, i < M → G.P.m + (i + 1) * (Fl.t + 1) + 1 = Nj i) (Ch : ∀ i, i < M → Type) [∀ i h, Finite (Ch i h)]
    (St : ∀ i (h : i < M), Ch i h → ChartG X (Nj i))

theorem levelsG_empty (j : ℕ) (hj : M < j) : IsEmpty ((levelsG X Fl M Nj hN Ch St).comp j) := by
  cases j with
  | zero => omega
  | succ j => exact ⟨fun c => absurd c.1 (by omega)⟩

set_option maxHeartbeats 2000000 in

def levelsG_tie (i : ℕ) (hi : i < M) (β : Ch i hi) :
    GChartTie X (levelsG X Fl M Nj hN Ch St) i (fun a : (St i hi β).comp => ⟨hi, β, a⟩)
      (St i hi β).J (St i hi β).Lb (St i hi β).Uloc (St i hi β).ψ (St i hi β).eps where
  em_inj := fun a b hab => by
    have h' : (⟨hi, β, a⟩ : (h : i < M) ×' Σ b : Ch i h, (St i h b).comp) = ⟨hi, β, b⟩ := hab
    simpa using h'
  rk := hN i hi
  fr := (St i hi β).fr
  fr_lat := (St i hi β).fr_lat
  yG := fun c => (St i hi β).rep c
  yG_p := fun c w' h => repG_over sp.cm.sig (St i hi β).J (St i hi β).Uloc p c w' h
  yG_bij := ⟨fun a b hab => by
      have h1 := repG_mk sp.cm.sig (St i hi β).J (St i hi β).Uloc p a
      have h2 := repG_mk sp.cm.sig (St i hi β).J (St i hi β).Uloc p b
      rw [← h1, ← h2]; exact hab,
    fun c => ⟨c, repG_mk sp.cm.sig (St i hi β).J (St i hi β).Uloc p c⟩⟩
  gamI := fun c => ((St i hi β).Gam c).subtype
  gamI_inj := fun c => Subtype.val_injective
  gamI_range := by
    intro c γ
    constructor
    · rintro ⟨g, rfl⟩
      exact g.2
    · intro h
      exact ⟨⟨γ, h⟩, rfl⟩
  act_eq := by
    intro c v w' h hw γ a b a' b' ha hb
    subst h
    have h2 : ∀ g : GL (Fin (G.P.m + (i + 1) * (Fl.t + 1) + 1)) (G.P.Qq v),
        (g : Matrix (Fin (G.P.m + (i + 1) * (Fl.t + 1) + 1)) (Fin (G.P.m + (i + 1) * (Fl.t + 1) + 1)) (G.P.Qq v)) a b =
        (castGL (hN i hi) (G.P.Qq v) g : Matrix (Fin (Nj i)) (Fin (Nj i)) (G.P.Qq v)) a' b' := by
      intro g
      rw [castGL_apply]
      have ea : a = Fin.cast (hN i hi).symm a' := Fin.ext ha
      have eb : b = Fin.cast (hN i hi).symm b' := Fin.ext hb
      rw [ea, eb]
    have h1 : castGL (hN i hi) (G.P.Qq v) (((levelsG X Fl M Nj hN Ch St).levS i ⟨hi, β, c⟩).act v γ) =
        bc (X.eQ v _ rfl).symm.toRingHom ((St i hi β).actW c v γ) := by
      show castGL (hN i hi) (G.P.Qq v) ((castGL (hN i hi) (G.P.Qq v)).symm _) = _
      rw [MulEquiv.apply_symm_apply]
      rfl
    rw [h2 (((levelsG X Fl M Nj hN Ch St).levS i ⟨hi, β, c⟩).act v γ), h1]
    show X.eQ v _ rfl ((X.eQ v _ rfl).symm _) = _
    rw [RingEquiv.apply_symm_apply]
    exact congrFun (congrFun (congrArg (fun g : GL (Fin (Nj i)) ((X.pl v).1.adicCompletion F) =>
      (g : Matrix (Fin (Nj i)) (Fin (Nj i)) ((X.pl v).1.adicCompletion F))) ((St i hi β).actW_apply c v γ)) a') b'
  chi_eq := by
    intro c γ x hx
    show (St i hi β).ψ (gamToUp sp.cm.sig (St i hi β).J (St i hi β).Up
      ((St i hi β).rep c : GL (Fin (Nj i)) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) γ) * (St i hi β).eps γ.1 =
        (St i hi β).ψ x * (St i hi β).eps γ.1
    congr 2
    apply Subtype.ext
    rw [hx]
    show (MulAut.conj ((St i hi β).rep c : GL (Fin (Nj i)) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))⁻¹) _ = _
    rw [MulAut.conj_apply, inv_inv]
    rfl

theorem levelsG_cover (i : ℕ) (hi : i < M) :
    ChartsCover (levelsG X Fl M Nj hN Ch St) i (fun (β : Ch i hi) (a : (St i hi β).comp) => ⟨hi, β, a⟩) :=
  ⟨fun x x' h => by
      obtain ⟨b, a⟩ := x
      obtain ⟨b', a'⟩ := x'
      have h' : (⟨hi, b, a⟩ : (h : i < M) ×' Σ b : Ch i h, (St i h b).comp) = ⟨hi, b', a'⟩ := h
      simpa using h',
    fun c => ⟨c.2, rfl⟩⟩

end Formalism.MainNotions.G.ChartsLv

end
