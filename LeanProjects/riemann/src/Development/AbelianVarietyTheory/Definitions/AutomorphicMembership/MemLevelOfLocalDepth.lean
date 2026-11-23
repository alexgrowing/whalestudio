import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfOrderDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCentralIdempotentOfGoodSeriesIdempotent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.Model

theorem mem_iff_trace {K G : Type} [Field K] [CharZero K] [Group G] [Fintype G] (X : Finset (G → K))
    (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (χ : G → K) :
    χ ∈ X ↔ IsAbsIrrChar χ ∧ ∑ g, (idemOf X).coeff g * χ g = χ 1 := by
  classical
  have hN : ((Fintype.card G : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have key : IsAbsIrrChar χ → χ 1 ≠ 0 ∧ ∑ g, (idemOf X).coeff g * χ g = if χ ∈ X then χ 1 else 0 := fun h => by
    have h1 : χ 1 ≠ 0 := by
      obtain ⟨n, ρ, hρ, hχ⟩ := h
      intro e
      have h2 := hχ 1
      rw [e, map_zero, Representation.char_one, Nat.cast_eq_zero, Module.finrank_zero_iff] at h2
      exact (bot_ne_top (α := Subrepresentation ρ)) (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
    refine ⟨h1, ?_⟩
    simp only [coeff_idemOf, Finset.sum_mul]
    rw [Finset.sum_comm, ← Finset.sum_ite_eq' X χ fun _ => χ 1]
    refine Finset.sum_congr rfl fun ψ hψ => ?_
    have h3 := conv_char (hX ψ hψ) h 1
    simp only [mul_one] at h3
    apply mul_right_cancel₀ h1
    simp only [mul_assoc, ← Finset.mul_sum]
    rw [h3]
    split_ifs with e
    · rw [e]; field_simp
    · simp
  refine ⟨fun h => ⟨hX χ h, by rw [(key (hX χ h)).2, if_pos h]⟩, fun ⟨h, e⟩ => ?_⟩
  by_contra hn
  rw [(key h).2, if_neg hn] at e
  exact (key h).1 e.symm

section Base

variable {B : Base} {px : PreX B.toPre} (I : ColIn B px)

theorem mem_vGs_iff (h : I.Ok) (P : HeightOneSpectrum (𝓞 B.fields.E)) : P ∈ (B.primes px).vGs ↔ ∃ k, I.C.P.Div k P := by
  classical
  unfold Formalism.L2.Col.Primes.vGs
  rw [Finset.mem_union, h.pibar, h.pibar, Fin.exists_fin_two]

theorem ixOf_empty (t : TupU I ∅) : ixOf I ∅ t = I.mu0 := by
  rcases (mem_range_ixOf I (U := ∅) (a := ixOf I ∅ t)).1 ⟨t, rfl⟩ with e | e
  · exact e
  · exact e.elim

theorem exists_under_of_selHalf (h : SelHalf I) (p : ℕ) (hp : p.Prime) :
    ∃ 𝔭 : HeightOneSpectrum (𝓞 B.host.K), ∀ a, ∀ P : HeightOneSpectrum (𝓞 B.host.E), P ∈ I.Q a →
      ((p : ℕ) : 𝓞 B.host.E) ∈ P.asIdeal → P.under (𝓞 B.host.K) = 𝔭 := by
  by_cases e : ∃ a, ∃ P : HeightOneSpectrum (𝓞 B.host.E), P ∈ I.Q a ∧ ((p : ℕ) : 𝓞 B.host.E) ∈ P.asIdeal
  · obtain ⟨b, P', hb, hP'⟩ := e
    exact ⟨P'.under (𝓞 B.host.K), fun a P ha hP => HeightOneSpectrum.ext (h a b P ha P' hb ⟨p, hp, hP, hP'⟩)⟩
  · exact ⟨I.C.P.pb 0, fun a P ha hP => absurd ⟨a, P, ha, hP⟩ e⟩

theorem mem_level_of_local_depth (g : Gc B px) : g ∈ lev0 I ↔ ∀ w, g w ∈ unip (kP w.1) B.R.r :=
  ⟨fun h w => h w (Set.mem_univ _), fun h w _ => h w⟩

theorem baseLevel_eq_unipotent : lev0 I = (Formalism.L2.Col.rP0 (R := B.R) I.Ch).grp := by
  ext g
  rw [mem_level_of_local_depth]
  refine ⟨fun h w _ => ⟨fun i j hij => unip_lower (h w) ?_, fun i _ => unip_diag (h w) i⟩, fun h w =>
    ⟨fun i j hij => (h w (Set.mem_univ _)).1 ?_, fun i => (h w (Set.mem_univ _)).2 i i.2⟩⟩
  · exact (Formalism.L2.Col.fine_lt_right i.2).1 hij
  · exact (Formalism.L2.Col.fine_lt_right i.2).2 hij

theorem isGenericPsi_psiC (h : I.Ok) : IsGenericPsi (B.primes px).vGs (psiC I) := fun P hP => by
  rw [psiC_of_mem I hP]
  exact h.ch_ok.psi_zero_nontrivial_character _

theorem embLL_xiValOf_of_ok (h : I.Ok) (a : I.ι) (P : HeightOneSpectrum (𝓞 B.fields.E)) :
    B.embLL (xiValOf I (I.tup a) P : B.LL) = (((I.xi a).val P : ℂˣ) : ℂ) :=
  embLL_xiValOf I a P ⟨_, (h.xi_reads a _).symm⟩

theorem valsIn_iff (h : I.Ok) : ValsIn I ↔ ∀ a, ∀ P ∈ I.Q a, ∃ z : B.LL, IsPrimitiveRoot z (Nat.card (kP P)) :=
  ⟨fun H => H.2, fun H => ⟨fun a _ _ => ⟨_, (h.xi_reads a _).symm⟩, H⟩⟩

end Base

section Record

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px)

theorem exists_levOf_of (h : I.Ok) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U))
    (hC : L.C = Top.Fr.at X I.C) (hx : L.xiH = fun t => I.xi (ixOf I U t)) (hQ : L.Q = fun t => I.Q (ixOf I U t))
    (hL : L.Is (mu0F (X := X.B.fields) (tuOf I U))) : ∃ L', LevOf X I U L' := by
  have hd : DiagSpaces X.toD7.sp := h.spaces
  obtain ⟨hst, hstX⟩ := GlobalTheory.Mem.HostFrames.stdLat_diag hd
  refine ⟨{ L with βX := 1, βV := fun _ => 1, ΛX := Formalism.IndefR.Seed.FrmP.coordL _, ΛV := fun _ => Formalism.IndefR.Seed.FrmP.coordL _ },
    ⟨⟨hL.mu0, hL.eta, hL.xi, hL.xi_inj, hL.xi_base, hL.xi_fin, hL.xi_triv, hL.xi_tame, hL.Pg, hL.Q_pl, hL.Q_off, hL.Q_de,
      hL.Q_ram, hL.chi, hL.xiR, hL.βY, Formalism.IndefR.Seed.FrmP.isSDFrame_std _ hstX 1,
      fun i => Formalism.IndefR.Seed.FrmP.isSDFrame_std _ (hst _).2.1 1, hL.βW⟩, hC, fun t => congrFun hx t, ?_,
      fun t => congrFun hQ t, fun _ => rfl, rfl⟩⟩
  refine Finset.ext fun P => (hL.Pg P).trans ?_
  rw [hC]
  exact (mem_vGs_iff I h P).symm

theorem exists_levOf_empty (h : I.Ok) : ∃ L, LevOf X I ∅ L := by
  have hx : ∀ t : TupU I ∅, I.xi (ixOf I ∅ t) = 1 := fun t => by rw [ixOf_empty, h.trueColumnChoices_heckeChar_reference_eq_one]
  have hQ : ∀ t : TupU I ∅, I.Q (ixOf I ∅ t) = ∅ := fun t => by rw [ixOf_empty, I.twistPrimes_reference_tuple_eq_empty]
  have hn : ∀ (t : TupU I ∅) (P : Pl X.toD7.host.E), P ∉ I.Q (ixOf I ∅ t) := fun t P => by
    rw [hQ]; exact Finset.notMem_empty _
  obtain ⟨L, h1, h2, h3, -, h4⟩ := GlobalTheory.LevelChoices.exists_levCh X.toD7 (Top.Fr.at X I.C) (TupU I ∅)
    (mu0F (X := X.B.fields) (tuOf I ∅)) (fun t => I.xi (ixOf I ∅ t)) (fun t => I.Q (ixOf I ∅ t))
    (h.xi_inj.comp (ixOf_injective I ∅)) (hx _)
    (fun t => ⟨1, one_pos, by rw [hx]; exact one_pow 1⟩)
    (fun t => by rw [hx]; exact (Formalism.L2.Host.isPsi_one (H := X.toD7.host) 2).triv)
    (fun t => by rw [hx]; exact fun _ _ _ _ => rfl)
    (fun t P hP => absurd hP (hn t P)) (fun t P hP => absurd hP (hn t P))
    (fun _ _ => ⟨I.C.P.pb 0, fun t P hP => absurd hP (hn t P)⟩)
    (fun t P => by
      rw [hx]
      exact iff_of_false (fun h => h fun _ _ => rfl) (by
        rintro (e | ⟨P', e, -⟩)
        exacts [hn t _ e, hn t _ e]))
  exact exists_levOf_of X I h ∅ L h1 h2 h3 h4

theorem grpAt_iff (h : I.Ok) : GrpAt X I ↔ ∀ k v, I.C.P.Div k (X.toD7.naut.plGw k v) := by
  classical
  refine ⟨fun ⟨⟨plg, hp⟩, _, _⟩ k v => (hp ⟨k, v⟩).1 ▸ (hp ⟨k, v⟩).2, fun H => ?_⟩
  obtain ⟨hc, hi⟩ := GlobalTheory.GoodLatCompare.goodSeriesIdempotent_central_idempotent X.toD7
  refine ⟨?_, hi, hc⟩
  have hPr := (base_fields_primes_ok X.B px).2.1
  let φ : (Σ k : Fin 2, X.toD7.nd.PlG k) → (X.B.primes px).vGs :=
    fun kv => ⟨X.toD7.naut.plGw kv.1 kv.2, (mem_vGs_iff I h _).2 ⟨kv.1, H _ _⟩⟩
  have hinj : Function.Injective φ := by
    rintro ⟨k, v⟩ ⟨k', v'⟩ e
    have e' : X.toD7.naut.plGw k v = X.toD7.naut.plGw k' v' := congrArg Subtype.val e
    have hk : k = k' := by
      have a := hPr.vG_norm k _ ((h.pibar k _).2 (H k v))
      have b := hPr.vG_norm k' _ ((h.pibar k' _).2 (H k' v'))
      have c : (X.B.primes px).g k = (X.B.primes px).g k' := a.symm.trans ((congrArg (fun P : HeightOneSpectrum (𝓞 X.B.fields.E) => Ideal.absNorm P.asIdeal) e').trans b)
      have := hPr.g_ne
      fin_cases k <;> fin_cases k' <;> first | rfl | exact absurd c this | exact absurd c.symm this
    subst hk
    rw [X.toD7.naut.plGw_inj k e']
  have hsurj : Function.Surjective φ := by
    rintro ⟨P, hP⟩
    obtain ⟨k, hk⟩ := (mem_vGs_iff I h P).1 hP
    let ψ : X.toD7.nd.PlG k → (X.B.primes px).vG k := fun v => ⟨X.toD7.naut.plGw k v, (h.pibar k _).2 (H k v)⟩
    have hψ : Function.Bijective ψ := by
      refine (Fintype.bijective_iff_injective_and_card ψ).2 ⟨fun v v' e => X.toD7.naut.plGw_inj k (congrArg Subtype.val e), ?_⟩
      rw [X.toD7.nd.card_PlG k, Fintype.card_coe, hPr.vG_card k]
      exact (X.toD7.what₂.card_Tau).symm
    obtain ⟨v, hv⟩ := hψ.2 ⟨P, (h.pibar k P).2 hk⟩
    exact ⟨⟨k, v⟩, Subtype.ext (by have := congrArg Subtype.val hv; exact this)⟩
  exact ⟨Equiv.ofBijective φ ⟨hinj, hsurj⟩, fun kv => ⟨rfl, H _ _⟩⟩

theorem grpAt_of_grpTrue (h : I.Ok) (hN : Top.GrpTrue X.N I.C) : GrpAt X I := (grpAt_iff X I h).2 hN.pl

theorem goodSet_of_idem (eR : Gc X.B px ≃* G0g X.toD7.nd) (Xg : Finset (Gc X.B px → X.B.LL)) (hX : ∀ χ ∈ Xg, IsAbsIrrChar χ)
    (he : ∀ g, X.B.embLL ((idemOf Xg).coeff g) = X.toD7.ntypes.e0.coeff (eR g)) : GoodSet X (px := px) eR Xg := by
  refine (goodSet_iff X eR Xg).2 ⟨fun χ => ?_, he⟩
  simp only [← he, ← map_mul, ← map_sum, X.B.embLL.injective.eq_iff]
  exact mem_iff_trace Xg hX χ

theorem GoodSet.nonempty {eR : Gc X.B px ≃* G0g X.toD7.nd} {Xg : Finset (Gc X.B px → X.B.LL)}
    (h : GoodSet X (px := px) eR Xg) (h0 : X.toD7.ntypes.e0 ≠ 0) : Xg.Nonempty := by
  by_contra e
  rw [Finset.not_nonempty_iff_eq_empty] at e
  apply h0
  apply MonoidAlgebra.ext
  ext t
  obtain ⟨g, rfl⟩ := eR.surjective t
  rw [← h.2 g, e]
  simp [idemOf]

theorem isIdG_iff (eG : Gc X.B px ≃* Gc X.B px) :
    IsPlacewiseIdentity X (px := px) (Pg := (X.B.primes px).vGs) eG ↔ eG = MulEquiv.refl _ :=
  ⟨fun h => MulEquiv.ext fun g => funext fun P => h g P.1 P.2 P.2, fun h => h ▸ isIdG_refl X⟩

end Record

end GlobalTheory.Mem.R3.Model

end
