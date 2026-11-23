import Formalism.LocalToGlobal.Columns.LocalLevelIsKOneAtT
import Formalism.LocalToGlobal.Columns.TiedAtT

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Repack0

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {sp : Spaces R F E} {gp : Fin 2 → ℕ} {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
  {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} {bad : Set (HeightOneSpectrum (𝓞 F))}

def LevPack.toCol (P : LevPack sp.cm R.k sp.gram0 gp A.T R.f bad (C.stab 0) fun c => sp.crdLat0 (clsLat 0 c))
    (spl : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (spl_sig : ∀ i v h x, spl i v h (sigR sp.cm.sig (v.adicCompletion F) x) = swapR _ (spl i v h x))
    (hiw : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal),
      ∀ x ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F), x ∈ P.lev.Uloc v ↔
        (1 : GL (Fin R.k) (v.adicCompletion F))⁻¹ * bc ((RingHom.fst _ _).comp (spl i v h).toRingHom) x * 1 ∈ iwU F R.k v)
    (w1 : HeightOneSpectrum (𝓞 F)) (reflection_mem_Glev_castSucc : (gp 0 : 𝓞 F) ∈ w1.asIdeal) :
    ColLevel R F E sp gp C A clsLat where
  Lb := P.lev.Lb
  Lb_fin := P.lev.Lb_fin
  Lb_span := P.lev.Lb_span
  Lb_int := P.lev.Lb_int
  Lb_dual := P.lev.Lb_dual
  Lb_index := P.lev.Lb_index
  Uloc := P.lev.Uloc
  Uloc_le := P.lev.Uloc_le
  Uloc_lev := P.lev.Uloc_lev
  Uloc_hyp := fun v h0 h1 hT => P.lev.Uloc_hyp v (fun hb => ((P.bad_iff v).1 hb).elim h0 h1) hT
  splitG := spl
  splitG_sig := spl_sig
  frG := fun _ _ _ => 1
  Uloc_g := hiw
  fM := P.lev.fM
  fT := P.lev.fT
  fT_ne := P.lev.fT_ne
  fT_T := P.lev.fT_T
  fM_card := P.lev.fM_card
  fT_L := P.lev.fT_L
  UlocAlt := P.lev.UlocAlt
  U := P.lev.U
  U_eq := P.lev.U_eq
  U_compact := P.lev.U_compact
  U_open := P.lev.U_open
  w1 := w1
  reflection_mem_Glev_castSucc := reflection_mem_Glev_castSucc
  y := P.cls.y
  y_bij := P.cls.y_bij
  y_lat := P.cls.y_lat
  stabI := P.cls.stabI
  stabI_inj := P.cls.stabI_inj
  stabI_range := P.cls.stabI_range
  stabI_lat := P.cls.stabI_lat

end Repack0

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)
  (spl : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)), (Pr.g i : 𝓞 X.F) ∈ v.asIdeal →
      X.E ⊗[X.F] v.adicCompletion X.F ≃+* v.adicCompletion X.F × v.adicCompletion X.F)

def IwLoc : Prop :=
  ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal),
    ∀ x ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) X.E) (v.adicCompletion X.F), x ∈ levLoc hc n (Pr.vT u) Pr.vGs Λ.grp v ↔
      (1 : GL (Fin n) (v.adicCompletion X.F))⁻¹ * bc ((RingHom.fst _ _).comp (spl i v h).toRingHom) x * 1 ∈ iwU X.F n v

variable (c₀ : DiaG X.E (Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet X.E n (Pr.vT u) Pr.vGs)

theorem levPack_iw (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (hK : LocalLevelIsKOneAtT hc u Λ) (hI : IwLoc hc u Λ spl) (H : HCrd Pr n fun c => (s c).1.L) :
    ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal),
      ∀ x ∈ UPts hc.sig H.J (v.adicCompletion X.F), x ∈ (levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.Uloc v ↔
        (1 : GL (Fin H.n') (v.adicCompletion X.F))⁻¹ * bc ((RingHom.fst _ _).comp (spl i v h).toRingHom) x * 1 ∈ iwU X.F H.n' v := by
  obtain ⟨n', hn, J, rfl, f, rfl, bad, rfl, lat, hlat⟩ := H
  subst hn
  obtain rfl : lat = fun c => (s c).1.L := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  exact hI

def th_resMap (P : Pl X.E) : 𝓞 X.F ⧸ (underPl X.F P).asIdeal →+* 𝓞 X.E ⧸ P.asIdeal :=
  Ideal.quotientMap P.asIdeal (algebraMap (𝓞 X.F) (𝓞 X.E)) (le_of_eq rfl)

include hPr in
theorem th_resMap_bij (P : {P // P ∈ Pr.vT u}) : Function.Bijective (th_resMap (X := X) P.1) := by
  constructor
  · exact Ideal.quotientMap_injective' (le_of_eq rfl)
  · intro b
    haveI : Fact (Pr.T u).Prime := ⟨hPr.T_prime u⟩
    haveI : Nontrivial (𝓞 X.E ⧸ P.1.asIdeal) := Ideal.Quotient.nontrivial_iff.2 P.1.isPrime.ne_top
    have hcard : Nat.card (𝓞 X.E ⧸ P.1.asIdeal) = Pr.T u := hPr.vT_norm u P.1 P.2
    obtain ⟨k, hk⟩ := mem_zmultiples_of_prime_card hcard (g := (1 : 𝓞 X.E ⧸ P.1.asIdeal)) (g' := b) one_ne_zero
    refine ⟨(k : 𝓞 X.F ⧸ (underPl X.F P.1).asIdeal), ?_⟩
    rw [map_intCast, ← hk]
    simp

def tieFv (P : {P // P ∈ Pr.vT u}) : (𝓞 X.E ⧸ P.1.asIdeal) ≃+* (𝓞 X.F ⧸ (tieEV hc hX hPr u P).1.asIdeal) :=
  (RingEquiv.ofBijective (th_resMap (X := X) P.1) (th_resMap_bij hPr u P)).symm

theorem tieFv_mk (P : {P // P ∈ Pr.vT u}) (x : 𝓞 X.F) :
    tieFv hc hX hPr u P (Ideal.Quotient.mk P.1.asIdeal (algebraMap (𝓞 X.F) (𝓞 X.E) x)) = Ideal.Quotient.mk _ x :=
  (RingEquiv.ofBijective (th_resMap (X := X) P.1) (th_resMap_bij hPr u P)).symm_apply_apply (Ideal.Quotient.mk _ x)

include hX hPr in

theorem exists_place_over_first_prime : ∃ v : HeightOneSpectrum (𝓞 X.F), (Pr.g 0 : 𝓞 X.F) ∈ v.asIdeal := by
  have hcard : 0 < (Pr.vG 0).card := by rw [hPr.vG_card 0]; exact hX.f_pos
  obtain ⟨P, hP⟩ := Finset.card_pos.1 hcard
  refine ⟨underPl X.F P, ?_⟩
  show (Pr.g 0 : 𝓞 X.F) ∈ P.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E))
  rw [Ideal.mem_comap, map_natCast, ← hPr.piG_norm 0]
  exact Ideal.mul_mem_left _ _ (decoFin_mem_of_mem_divs hP)

end Gen

end Formalism.L2.Col
