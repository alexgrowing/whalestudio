import Formalism.LocalToGlobal.GroupLattices.LevelCharts.LevelsOfTie

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
  {L : ColLevel R F E sp gp C A clsLat}

structure GChartTie {p : ℕ} {G : GAtP p} (X : Formalism.L2.Herm.GLevTie L G) {Fl : Fills G} (Lv : Levels Fl) (i : ℕ) {cmp : Type}
    (em : cmp → Lv.compS i) {N : ℕ}
    (J : Matrix (Fin N) (Fin N) E) (Lb : Submodule (𝓞 E) (Fin N → E))
    (Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F)))
    (ψ : awayG sp.cm.sig J Uloc p →* G.Oˣ) (eps : UJ (sp.cm.sig : E →+* E) J →* G.Oˣ) where

  em_inj : Function.Injective em

  rk : (Fl.Pj (i + 1)).m + 1 = N

  fr : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal → GL (Fin N) (w.adicCompletion F)
  fr_lat : ∀ w h (t : Fin N → w.adicCompletion F),
    (∃ x ∈ Formalism.L2.Herm.locL w Lb, ∀ a, (X.spl w h (x a)).1 = t a) ↔
      ∀ a, (((fr w h)⁻¹ : GL (Fin N) (w.adicCompletion F)) :
        Matrix (Fin N) (Fin N) (w.adicCompletion F)).mulVec t a ∈ w.adicCompletionIntegers F

  yG : cmp → UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F)
  yG_p : ∀ c (w : HeightOneSpectrum (𝓞 F)), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal →
    bc (prV (E := E) w) (yG c : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) = 1
  yG_bij : Function.Bijective (fun c : cmp => (Quotient.mk'' (yG c) : compG sp.cm.sig J Uloc p))

  gamI : ∀ c, (Lv.levS i (em c)).Γ →* UJ (sp.cm.sig : E →+* E) J
  gamI_inj : ∀ c, Function.Injective (gamI c)
  gamI_range : ∀ c (γ : UJ (sp.cm.sig : E →+* E) J), γ ∈ (gamI c).range ↔
    bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin N) E) ∈
      (awayG sp.cm.sig J Uloc p).map (MulAut.conj (yG c : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))).toMonoidHom

  act_eq : ∀ c (v : Fin G.P.nV) w (h : (X.pl v).1 = w) (hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal) (γ : (Lv.levS i (em c)).Γ)
    (a b : Fin ((Fl.Pj (i + 1)).m + 1)) (a' b' : Fin N), (a : ℕ) = a' → (b : ℕ) = b' →
    X.eQ v w h (((Lv.levS i (em c)).act v γ : GL (Fin ((Fl.Pj (i + 1)).m + 1)) (G.P.Qq v)) a b) =
      (((fr w hw)⁻¹ * bc ((RingHom.fst _ _).comp (X.spl w hw).toRingHom)
        (bc (inclE (F := F) (w.adicCompletion F)) (gamI c γ : GL (Fin N) E)) * fr w hw :
          GL (Fin N) (w.adicCompletion F)) : Matrix (Fin N) (Fin N) (w.adicCompletion F)) a' b'

  chi_eq : ∀ c (γ : (Lv.levS i (em c)).Γ) (x : awayG sp.cm.sig J Uloc p),
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) =
      (yG c : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))⁻¹ *
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (gamI c γ : GL (Fin N) E) * yG c →
    (Lv.levS i (em c)).χ γ = ψ x * eps (gamI c γ)

variable {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]
  {n' : ℕ} {O Kf : Type} [IsDomain W] [IsDiscreteValuationRing W]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ}

set_option maxHeartbeats 2000000 in

def levelsOfCh_tie (hS : HidaSetting p n' W Qq O Kf ι σ j w) (r : ℕ)
    (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ) (dom : ∀ v, IsDominant (lam0 v)) (hk : m + 1 = R.k)
    (I : LocId L p nV W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ)
    (y : compL L p → UPts sp.cm.sig sp.gram0 (Formalism.L2.Herm.Af F)) [Finite (compL L p)] (e : ℕ)
    (hy : ∀ i, (Quotient.mk'' (y i) : compL L p) = i)
    (hyp : ∀ i (w' : HeightOneSpectrum (𝓞 F)), ((p : ℕ) : 𝓞 F) ∈ w'.asIdeal →
      bc (prV (E := E) w') (y i : GL (Fin R.k) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1)
    (Fl : Fills (gatOfLevel L hS nV r lam0 dom hk I ψ y e)) (M : ℕ) (Nj : ℕ → ℕ)
    (hN : ∀ i, i < M → m + (i + 1) * (Fl.t + 1) + 1 = Nj i) (Ch : ∀ i, i < M → Type) [∀ i h, Finite (Ch i h)]
    (St : ∀ i (h : i < M), Ch i h → StepAt I O (Nj i)) (i : ℕ) (hi : i < M) (β : Ch i hi) :
    GChartTie (gatOfLevel_tie L hS nV r lam0 dom hk I ψ y e hy hyp)
      (levelsOfCh hS r lam0 dom hk I ψ y e Fl M Nj hN Ch St) i (fun a : (St i hi β).comp => ⟨hi, β, a⟩)
      (St i hi β).J (St i hi β).Lb (St i hi β).Uloc (St i hi β).ψ (St i hi β).eps where
  em_inj := fun a b hab => by
    simpa using hab
  rk := hN i hi
  fr := (St i hi β).fr.fr
  fr_lat := (St i hi β).fr.fr_lat
  yG := fun c => (St i hi β).rep c
  yG_p := fun c w' h => repG_over sp.cm.sig (St i hi β).J (St i hi β).Uloc p c w' h
  yG_bij := ⟨fun a b hab => by
      have h1 := repG_mk sp.cm.sig (St i hi β).J (St i hi β).Uloc p a
      have h2 := repG_mk sp.cm.sig (St i hi β).J (St i hi β).Uloc p b
      rw [← h1, ← h2]; exact hab,
    fun c => ⟨c, repG_mk sp.cm.sig (St i hi β).J (St i hi β).Uloc p c⟩⟩
  gamI := fun c => (gamC sp.cm.sig (St i hi β).J (St i hi β).Up
    ((St i hi β).rep c : GL (Fin (Nj i)) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))).subtype
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
    have h1 := levC_act sp.cm.sig (St i hi β).J (St i hi β).Up hS nV r
      (fun v s => liftWt Fl.t m (lam0 v s) (fun a => Fl.w v a s) (i + 1)) (Fl.domJ (i + 1)) (hN i hi) I.iw (St i hi β).fr.frQ
      (St i hi β).ψ ((St i hi β).rep c : GL (Fin (Nj i)) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) v γ
    have h2 : ∀ g : GL (Fin (m + (i + 1) * (Fl.t + 1) + 1)) Qq,
        (g : Matrix (Fin (m + (i + 1) * (Fl.t + 1) + 1)) (Fin (m + (i + 1) * (Fl.t + 1) + 1)) Qq) a b =
        (castGL (hN i hi) Qq g : Matrix (Fin (Nj i)) (Fin (Nj i)) Qq) a' b' := by
      intro g
      rw [castGL_apply]
      have ea : a = Fin.cast (hN i hi).symm a' := Fin.ext ha
      have eb : b = Fin.cast (hN i hi).symm b' := Fin.ext hb
      rw [ea, eb]
    have h3 : ((St i hi β).fr.frQ v)⁻¹ * bc (I.iw v) (gamMat sp.cm.sig (St i hi β).J (St i hi β).Up
          ((St i hi β).rep c : GL (Fin (Nj i)) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) γ) * (St i hi β).fr.frQ v =
        bc (I.eQ v).symm.toRingHom (((St i hi β).fr.fr (I.pl v).1 (I.pl v).2)⁻¹ *
          bc ((RingHom.fst _ _).comp (I.spl (I.pl v).1 (I.pl v).2).toRingHom)
            (bc (inclE (F := F) ((I.pl v).1.adicCompletion F)) (gamMat sp.cm.sig (St i hi β).J (St i hi β).Up
              ((St i hi β).rep c : GL (Fin (Nj i)) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) γ)) *
                (St i hi β).fr.fr (I.pl v).1 (I.pl v).2) := by
      rw [map_mul, map_mul, map_inv]
      rfl
    show I.eQ v _ = _
    rw [h2 (((levelsOfCh hS r lam0 dom hk I ψ y e Fl M Nj hN Ch St).levS i ⟨hi, β, c⟩).act v γ)]
    erw [h1]
    rw [h3]
    show I.eQ v ((I.eQ v).symm _) = _
    rw [RingEquiv.apply_symm_apply]
    rfl
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

theorem levelsOfCh_cover (hS : HidaSetting p n' W Qq O Kf ι σ j w) (r : ℕ)
    (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ) (dom : ∀ v, IsDominant (lam0 v)) (hk : m + 1 = R.k)
    (I : LocId L p nV W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ)
    (y : compL L p → UPts sp.cm.sig sp.gram0 (Formalism.L2.Herm.Af F)) [Finite (compL L p)] (e : ℕ)
    (Fl : Fills (gatOfLevel L hS nV r lam0 dom hk I ψ y e)) (M : ℕ) (Nj : ℕ → ℕ)
    (hN : ∀ i, i < M → m + (i + 1) * (Fl.t + 1) + 1 = Nj i) (Ch : ∀ i, i < M → Type) [∀ i h, Finite (Ch i h)]
    (St : ∀ i (h : i < M), Ch i h → StepAt I O (Nj i)) (i : ℕ) (hi : i < M)
    (c : (levelsOfCh hS r lam0 dom hk I ψ y e Fl M Nj hN Ch St).compS i) :
    ∃! x : Σ β : Ch i hi, (St i hi β).comp, c = ⟨hi, x.1, x.2⟩ :=
  ⟨c.2, rfl, fun x hx => by rw [hx]⟩

def ChartsCover {p : ℕ} {G : GAtP p} {Fl : Fills G} (Lv : Levels Fl) (i : ℕ) {Cb : Type} {cmp : Cb → Type}
    (em : ∀ β, cmp β → Lv.compS i) : Prop :=
  Function.Bijective (fun x : Σ β, cmp β => em x.1 x.2)

theorem levelsOfCh_chartsCover (hS : HidaSetting p n' W Qq O Kf ι σ j w) (r : ℕ)
    (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ) (dom : ∀ v, IsDominant (lam0 v)) (hk : m + 1 = R.k)
    (I : LocId L p nV W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ)
    (y : compL L p → UPts sp.cm.sig sp.gram0 (Formalism.L2.Herm.Af F)) [Finite (compL L p)] (e : ℕ)
    (Fl : Fills (gatOfLevel L hS nV r lam0 dom hk I ψ y e)) (M : ℕ) (Nj : ℕ → ℕ)
    (hN : ∀ i, i < M → m + (i + 1) * (Fl.t + 1) + 1 = Nj i) (Ch : ∀ i, i < M → Type) [∀ i h, Finite (Ch i h)]
    (St : ∀ i (h : i < M), Ch i h → StepAt I O (Nj i)) (i : ℕ) (hi : i < M) :
    ChartsCover (levelsOfCh hS r lam0 dom hk I ψ y e Fl M Nj hN Ch St) i
      (fun (β : Ch i hi) (a : (St i hi β).comp) => ⟨hi, β, a⟩) :=
  ⟨fun x x' h => by
      obtain ⟨b, a⟩ := x
      obtain ⟨b', a'⟩ := x'
      simpa using h,
    fun c => ⟨c.2, rfl⟩⟩

end Formalism.L2.G
