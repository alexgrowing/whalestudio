import Development.EtaleCohomology.CohomologicalPurity.LeafIndExc
import Development.EtaleCohomology.CohomologicalPurity.LeafHensCutDef

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.CohomologicalPurity.Hz

theorem Good.nbhd {A S : Type} [CommRing A] [CommRing S] {φ : A →+* S} {I : Ideal A} (h : Good φ I) : Nbhd φ I := by
  refine ⟨h.etale, Ideal.quotientMap_injective' ?_, fun y => ?_⟩
  · obtain ⟨r, hr⟩ := h.retr
    have h1 : I.map φ ≤ RingHom.ker r := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      change (r.comp φ) a = 0
      rw [hr]
      exact Ideal.Quotient.eq_zero_iff_mem.2 ha
    intro a ha
    have h2 : (r.comp φ) a = 0 := h1 ha
    rw [hr] at h2
    exact Ideal.Quotient.eq_zero_iff_mem.1 h2
  · obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := h.surj s
    refine ⟨Ideal.Quotient.mk I a, ?_⟩
    rw [Ideal.quotientMap_mk]
    exact (Ideal.Quotient.eq.2 ha).symm

theorem exists_obj (h1 : LeafDiag) (h2 : LeafColHens) (h3 : LeafColUniv) (A : Type) [CommRing A] (I : Ideal A) :
    ∃ (H : CommRingCat.{0}) (η : A →+* H), HenselianRing H (I.map η) ∧ IndNbhd η I ∧ Univ η I := by
  obtain ⟨Δ⟩ := h1 A I
  let c := colimit.cocone Δ.D
  have hc : IsColimit c := colimit.isColimit Δ.D
  obtain ⟨j₀⟩ : Nonempty Δ.J := IsFiltered.nonempty
  have hw : ∀ {j k : Δ.J} (e : j ⟶ k), (Δ.leg c j).comp (Δ.s j) = (Δ.leg c k).comp (Δ.s k) := fun {j k} e => by
    have h : (Δ.leg c k).comp (Δ.D.map e).hom = Δ.leg c j := congrArg CommRingCat.Hom.hom (c.w e)
    rw [← Δ.nat e, ← RingHom.comp_assoc, h]
  have hη : ∀ j, (Δ.leg c j).comp (Δ.s j) = (Δ.leg c j₀).comp (Δ.s j₀) := fun j =>
    (hw (IsFiltered.leftToMax j j₀)).trans (hw (IsFiltered.rightToMax j j₀)).symm
  refine ⟨c.pt, _, h2 A I Δ c hc _ hη, ?_, h3 A I Δ c hc _ hη⟩
  refine ⟨Δ.J, Δ.cat, Δ.filt, Δ.D, ⟨fun j => CommRingCat.ofHom (Δ.s j), fun j k e => ?_⟩, c.ι, ⟨hc⟩,
    fun j => ⟨(Δ.good j).nbhd, ?_⟩⟩
  · exact CommRingCat.hom_ext (Δ.nat e).symm
  · exact CommRingCat.hom_ext (hη j)

theorem goal_of (h1 : LeafDiag) (h2 : LeafColHens) (h3 : LeafColUniv) : LeafHens := by
  choose H η hh hi hu using exists_obj h1 h2 h3
  have key : ∀ {A B : Type} [CommRing A] [CommRing B] {I : Ideal A} {J : Ideal B} (φ : A →+* B), I ≤ J.comap φ →
      ∃! χ : H A I →+* H B J, χ.comp (η A I) = (η B J).comp φ := fun {A B} _ _ {I J} φ h =>
    hu A I _ _ (hh B J) _ fun a ha => Ideal.mem_map_of_mem (η B J) (h ha)
  refine ⟨⟨H, η, fun φ h => (key φ h).exists.choose, fun φ h => (key φ h).exists.choose_spec, fun A _ I h => ?_,
    fun φ ψ h h' h'' => ?_, hh, hi⟩⟩
  · exact (key _ h).unique (key _ h).exists.choose_spec rfl
  · refine (key _ h'').unique (key _ h'').exists.choose_spec ?_
    rw [RingHom.comp_assoc, (key φ h).exists.choose_spec, ← RingHom.comp_assoc, (key ψ h').exists.choose_spec,
      RingHom.comp_assoc]

end LateralTheory.CohomologicalPurity.Hz
